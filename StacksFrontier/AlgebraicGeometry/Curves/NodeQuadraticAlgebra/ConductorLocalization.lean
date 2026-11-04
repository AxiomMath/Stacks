module

public import StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk

/-!
# The normalization of a curve, localized at one node

Let `A` be a reduced ring with finitely many minimal primes, let
`A' = integralClosure A (FractionRing A)` be its normalization inside its total ring of
fractions, and let `C` be a localization of `A` at a submonoid `M`. Then the localization of
`A'` at the image of `M` is the normalization of `C`: it is the integral closure of `C` in the
total ring of fractions of `C`, as a `C`-algebra and hence compatibly with the maps from `A`.

Taking `M = 𝔪.primeCompl` for a prime `𝔪` of `A`, this says that the semilocal ring
`A' ⊗_A A_𝔪` is the integral closure of the stalk `𝒪_{X, x} = A_𝔪` in its total ring of
fractions. That is the identification the node-local computations of
`StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor` need in order to say
anything about `A'`: those computations are carried out at a local ring, whereas an affine cover
of a nodal curve supplies a global `A` together with a singular point of `Spec A`. The two
consequences recorded here are, at a node `𝔪`:

* the image of `A_𝔪` in `A' ⊗_A A_𝔪` is a coatom in the lattice of `A_𝔪`-submodules, so the
  quotient is simple; and
* the conductor contains `𝔪`, in the form `𝔪 (A' ⊗_A A_𝔪) ⊆ A_𝔪`.

Both are stated at a single node, which is the granularity their consumer needs: the residues at
the two branches of a node can be normalised independently only one node at a time.

## Main results

* `Stacks.Curves.isArtinianRing_fractionRing`: the total ring of fractions of a reduced ring
  with finitely many minimal primes is Artinian.
* `Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`: the localization
  of `A'` is the integral closure of the localization of `A`.
* `Stacks.Curves.isCoatom_range_algebraMap_localization_integralClosure_of_isNodalAlgebra`: at a
  node, the image of the local ring in the localized normalization is a coatom.
* `Stacks.Curves.map_maximalIdeal_le_range_algebraMap_localization_integralClosure`: at a node,
  the maximal ideal times the localized normalization lies in the image of the local ring.

## Implementation notes

The localization of `A'` at the image of `M` is `Localization (Algebra.algebraMapSubmonoid A' M)`,
and its `C`-algebra structure is the comparison map `localizationAlgebra` of a localization of an
algebra, which therefore has to be supplied in every statement about it. The isomorphism is
stated as `Nonempty (_ ≃ₐ[C] _)` so that no choice of comparison map enters the statement.

The ambient ring is `FractionRing A` throughout, rather than `FractionRing (A ⧸ nilradical A)`:
the two agree for a reduced `A`, and the former is the one the node computations and
`Ring.deltaInvariant` are stated with. Using it directly avoids passing through the reduction, at
the cost of having to know that `FractionRing A` is Artinian, which for a reduced ring with
finitely many minimal primes is its decomposition as a finite product of fraction fields.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- **The total ring of fractions of a reduced ring with finitely many minimal primes is
Artinian.** It is the product, over those primes, of the fraction fields of the corresponding
quotients, and a finite product of fields is Artinian. -/
public theorem isArtinianRing_fractionRing (A : Type*) [CommRing A] [IsReduced A]
    (hA : (minimalPrimes A).Finite) :
    IsArtinianRing (FractionRing A) := by
  have : Finite (minimalPrimes A) := hA
  let : (p : minimalPrimes A) → Algebra A (FractionRing (A ⧸ (p : Ideal A))) :=
    fun p => ((algebraMap (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))).comp
      (Ideal.Quotient.mk (p : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.totalFractionRing_algEquiv_pi_fractionRing_quotient hA
  exact e.symm.toRingEquiv.isArtinianRing

/-- **The normalization of a localization is the localization of the normalization.** Let `A` be
a reduced ring with finitely many minimal primes, let `A'` be its integral closure in its total
ring of fractions, and let `C` be the localization of `A` at a submonoid `M`. Then the
localization of `A'` at the image of `M` is the integral closure of `C` in the total ring of
fractions of `C`, as a `C`-algebra.

Being an isomorphism of `C`-algebras it is compatible with the maps from `A` as well, both sides
carrying the `A`-algebra structure obtained from `C` by composition. -/
public theorem nonempty_algEquiv_localization_integralClosure_fractionRing
    (A : Type*) [CommRing A] [IsReduced A] (hA : (minimalPrimes A).Finite)
    (C : Type*) [CommRing C] [Algebra A C] (M : Submonoid A) [IsLocalization M C] :
    letI : Algebra C (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) M)) :=
      localizationAlgebra M ↥(integralClosure A (FractionRing A))
    Nonempty (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) M) ≃ₐ[C]
      ↥(integralClosure C (FractionRing C))) := by
  let S := FractionRing A
  let T := ↥(integralClosure A S)
  let L := Localization (Algebra.algebraMapSubmonoid S M)
  let C' := Localization (Algebra.algebraMapSubmonoid T M)
  let : Algebra C L := localizationAlgebra M S
  have : IsScalarTower A C L := isScalarTower_localizationAlgebra M S
  let : Algebra C C' := localizationAlgebra M T
  have : IsScalarTower A C C' := isScalarTower_localizationAlgebra M T
  have : IsArtinianRing S := isArtinianRing_fractionRing A hA
  have : IsFractionRing C L := isFractionRing_localization_of_artinian (Q := S) M
  let e : C' ≃ₐ[C] ↥(integralClosure C L) :=
    AlgebraicGeometry.Scheme.integralClosureLocalizationEquiv M
      (AlgEquiv.refl (R := A) (A₁ := T))
  let eL : L ≃ₐ[C] FractionRing C :=
    IsLocalization.algEquiv (nonZeroDivisors C) L (FractionRing C)
  exact ⟨e.trans eL.mapIntegralClosure⟩

/-! ### Transfer of the node-local computations to a localization -/

/-- An isomorphism of algebras carries the image of the base onto the image of the base. -/
private theorem map_range_algebra_linearMap {R B D : Type*} [CommRing R] [CommRing B]
    [CommRing D] [Algebra R B] [Algebra R D] (e : B ≃ₐ[R] D) :
    Submodule.map (e.toLinearEquiv : B →ₗ[R] D) (LinearMap.range (Algebra.linearMap R B)) =
      LinearMap.range (Algebra.linearMap R D) := by
  rw [← LinearMap.range_comp]
  exact congrArg LinearMap.range (LinearMap.ext e.commutes)

/-- **At a node the image of the local ring in the localized normalization is a coatom.** Let
`A` be a reduced Noetherian ring over a field `k`, let `A'` be its integral closure in its total
ring of fractions, and let `𝔪` be a prime of `A` at which the local ring is a nodal `k`-algebra.
Then the image of `A_𝔪` in `A' ⊗_A A_𝔪` is a coatom in the lattice of `A_𝔪`-submodules, so the
quotient is simple.

This is `Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra`, a statement
about the integral closure of a local ring, transported to the localization of the integral
closure of `A` along
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`. -/
public theorem isCoatom_range_algebraMap_localization_integralClosure_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsReduced A] [IsNoetherianRing A]
    [Algebra k A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (hnodal : IsNodalAlgebra k (Localization.AtPrime 𝔪)) :
    letI : Algebra (Localization.AtPrime 𝔪) (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) 𝔪.primeCompl)) :=
      localizationAlgebra 𝔪.primeCompl ↥(integralClosure A (FractionRing A))
    IsCoatom (LinearMap.range (Algebra.linearMap (Localization.AtPrime 𝔪)
      (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) 𝔪.primeCompl)))) := by
  let C := Localization.AtPrime 𝔪
  have : IsNoetherianRing C := IsLocalization.isNoetherianRing 𝔪.primeCompl C inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_localization_integralClosure_fractionRing A
    (minimalPrimes.finite_of_isNoetherianRing A) C 𝔪.primeCompl
  have hcoatom : IsCoatom (LinearMap.range
      (Algebra.linearMap C ↥(integralClosure C (FractionRing C)))) :=
    isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k C hnodal
  rw [← map_range_algebra_linearMap e] at hcoatom
  exact ((Submodule.orderIsoMapComap e.toLinearEquiv).isCoatom_iff _).mp hcoatom

/-- **At a node the conductor contains the maximal ideal, after localizing.** With `A`, `A'` and
`𝔪` as above, the product of `𝔪` with the localization `A' ⊗_A A_𝔪` is contained in the image of
`A_𝔪`.

This is `Stacks.Curves.map_maximalIdeal_le_range_algebraMap_integralClosure` transported along
`Stacks.Curves.nonempty_algEquiv_localization_integralClosure_fractionRing`. -/
public theorem map_maximalIdeal_le_range_algebraMap_localization_integralClosure
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsReduced A] [IsNoetherianRing A]
    [Algebra k A] (𝔪 : Ideal A) [𝔪.IsPrime]
    (hnodal : IsNodalAlgebra k (Localization.AtPrime 𝔪)) :
    letI : Algebra (Localization.AtPrime 𝔪) (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure A (FractionRing A)) 𝔪.primeCompl)) :=
      localizationAlgebra 𝔪.primeCompl ↥(integralClosure A (FractionRing A))
    ∀ t ∈ (maximalIdeal (Localization.AtPrime 𝔪)).map
        (algebraMap (Localization.AtPrime 𝔪) (Localization (Algebra.algebraMapSubmonoid
          ↥(integralClosure A (FractionRing A)) 𝔪.primeCompl))),
      t ∈ LinearMap.range (Algebra.linearMap (Localization.AtPrime 𝔪)
        (Localization (Algebra.algebraMapSubmonoid
          ↥(integralClosure A (FractionRing A)) 𝔪.primeCompl))) := by
  let C := Localization.AtPrime 𝔪
  have : IsNoetherianRing C := IsLocalization.isNoetherianRing 𝔪.primeCompl C inferInstance
  obtain ⟨e⟩ := nonempty_algEquiv_localization_integralClosure_fractionRing A
    (minimalPrimes.finite_of_isNoetherianRing A) C 𝔪.primeCompl
  intro t ht
  have hmap : e t ∈ (maximalIdeal C).map (algebraMap C _) := by
    rw [← e.toAlgHom.comp_algebraMap, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ ht
  obtain ⟨c, hc⟩ := map_maximalIdeal_le_range_algebraMap_integralClosure k C hnodal hmap
  exact ⟨c, e.injective ((e.commutes c).trans hc)⟩

end Stacks.Curves

end
