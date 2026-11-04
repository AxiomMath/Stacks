module

public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor

/-!
# The forgetful functor of the small étale site preserves the fibre products of a covering

Let `S` be a scheme.  The forgetful functor `AlgebraicGeometry.Scheme.Etale.forget S` from the
small étale site of `S` to the schemes over `S` preserves the iterated fibre products of any
family in the small étale site, so the comparison maps from the images of those fibre products
to the fibre products of the image family are invertible.

## Main results

* `AlgebraicGeometry.smallEtaleStandardCoverings_isIso_cechProductMapOfFunctor`: for a covering
  in `AlgebraicGeometry.smallEtaleStandardCoverings`, the comparison map
  `Stacks.CechSite.cechProductMapOfFunctor` along `AlgebraicGeometry.Scheme.Etale.forget S` is an
  isomorphism.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- For a covering in `AlgebraicGeometry.smallEtaleStandardCoverings`, the comparison maps from
the images under `AlgebraicGeometry.Scheme.Etale.forget S` of its iterated fibre products to the
iterated fibre products of the image covering are isomorphisms. -/
public theorem smallEtaleStandardCoverings_isIso_cechProductMapOfFunctor :
    ∀ {U : S.Etale}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ Scheme.smallEtaleTopology S U })
      (hE : E ∈ smallEtaleStandardCoverings S U) (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
            smallEtaleStandardCoverings_hasProducts S E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map (Scheme.Etale.forget S)).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map (Scheme.Etale.forget S)).f (j a))) :=
            smallEtaleStandardCoverings_hasImageProducts S E hE
        IsIso (Stacks.CechSite.cechProductMapOfFunctor (Scheme.Etale.forget S) E.1 p i) := by
  intro U E hE p i
  let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.1.f (i a))))
      (Over.post (X := U) (Scheme.Etale.forget S)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (Scheme.Etale.forget S) E.1
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  exact Stacks.CechSite.isIso_cechProductMapOfFunctor (Scheme.Etale.forget S) E.1 p i

end AlgebraicGeometry
