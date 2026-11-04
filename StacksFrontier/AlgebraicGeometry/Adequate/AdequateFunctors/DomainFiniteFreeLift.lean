module

public import Mathlib.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainKernelPresentation
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.SymmetricAlgebraInSite

/-!
# Tag 06V0 on the algebras of a site

`AdequateFunctor.exists_lift_from_finite_free_kernel_on` carries [Stacks, Tag 06V0] to the
module-valued functors on a domain of algebras cut out by a property, given three inputs: the
domain contains the symmetric algebra on every finitely generated module, it contains the
Laurent polynomial algebra of each of its members, and it has a base object. This file
discharges all three for the algebras whose spectra have size below a cutoff, and so states
[Stacks, Tag 06V0] over the algebras of a site.

The size bounds are clauses (9)(b) and (9)(c) of [Stacks, Tag 000R]. The universal solution
module is a quotient of a finite free module, so it is finitely generated and the symmetric
algebra on it is of finite type: clause (9)(b). The Laurent polynomial algebra `R[T, T⁻¹]` is
the localization of `R[X]` at the powers of `X`, so it is clause (9)(b) followed by clause
(9)(c). The base object is the base ring itself, which is an algebra of the site exactly when
its spectrum is an object of the site.

Nothing about the cutoff beyond uncountability and `Cardinal.IsStrongPrelimit` is used, and both
are carried by every big site, so they are taken as hypotheses rather than extracted from a
chosen site here.

## Main results

* `AdequateFunctor.size_lt_of_spec_symmetricAlgebra` — the spectrum of the symmetric algebra on
  a finitely generated module over a ring whose spectrum is below the cutoff is again below it.
* `AdequateFunctor.size_lt_of_spec_laurentPolynomial` — the same for the Laurent polynomial
  algebra of a ring whose spectrum is below the cutoff.
* `AdequateFunctor.exists_lift_from_finite_free_kernel_site` — [Stacks, Tag 06V0] for the
  module-valued functors on the algebras of a site.

## Implementation notes

No `@[stacks]` attribute is placed here: the tagged statement of 06V0 is
`AdequateFunctor.exists_lift_from_finite_free_kernel`, over all commutative algebras, and these
are that statement transported to the algebras of a site.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace AdequateFunctor

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- The spectrum of the symmetric algebra on a finitely generated module over a ring whose
spectrum has size below an uncountable strong prelimit cutoff again has size below that cutoff:
the symmetric algebra is of finite type, so this is [Stacks, Tag 000R] (9)(b). -/
public theorem size_lt_of_spec_symmetricAlgebra (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    (V : Type u) [AddCommGroup V] [Module A V] [Module.Finite A V] :
    (Spec (CommRingCat.of (SymmetricAlgebra A V))).size < κ :=
  have : Algebra.FiniteType A (SymmetricAlgebra A V) := SymmetricAlgebra.finiteType A V
  Scheme.size_Spec_lt_of_finiteType hκ hsl A (SymmetricAlgebra A V) hA

include hκ hsl in
/-- The spectrum of the Laurent polynomial algebra of a ring whose spectrum has size below an
uncountable strong prelimit cutoff again has size below that cutoff: `R[T, T⁻¹]` is the
localization of `R[X]` at the powers of `X`, so this is [Stacks, Tag 000R] (9)(b) followed by
(9)(c). -/
public theorem size_lt_of_spec_laurentPolynomial (R : Type u) [CommRing R]
    (hR : (Spec (CommRingCat.of R)).size < κ) :
    (Spec (CommRingCat.of (LaurentPolynomial R))).size < κ :=
  have hpoly : (Spec (CommRingCat.of (Polynomial R))).size < κ :=
    Scheme.size_Spec_lt_of_finiteType hκ hsl R (Polynomial R) hR
  Scheme.size_Spec_lt_of_isLocalization hκ hsl
    (Submonoid.powers (Polynomial.X : Polynomial R)) (LaurentPolynomial R) hpoly

include hκ hsl in
/-- **Stacks Lemma 06V0 over the algebras of a site.** A morphism from the kernel of a morphism
between finite free module-valued functors on the algebras whose spectra have size below the
cutoff, to the module-valued functor of a module, extends to the middle finite free functor. -/
public theorem exists_lift_from_finite_free_kernel_site (A : Type u) [CommRing A]
    (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    (n m : ℕ)
    (L : ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)))
    (i : L ⟶ moduleExtensionOfCarrierOn.{max u w}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrierOn.{max u w}
        (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w}
        (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrierOn.{max u w}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) M)
    [Mono i] (hd : i ≫ d = 0) (h : (CategoryTheory.ShortComplex.mk i d hd).Exact) :
    ∃ ψ : moduleExtensionOfCarrierOn.{max u w}
        (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w}
        (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) M, i ≫ ψ = φ :=
  exists_lift_from_finite_free_kernel_on.{w} A M (algebraInSite A (schemeSizeBelow κ))
    (fun V => size_lt_of_spec_symmetricAlgebra hκ hsl A hA V)
    (fun R _ _ hR => size_lt_of_spec_laurentPolynomial hκ hsl R hR)
    (BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA) n m L i d φ hd h

include hκ hsl in
/-- **Stacks Lemma 06V3 over the algebras of a site, for a linearly adequate source.** The
kernel of a morphism from a linearly adequate module-valued functor on the algebras of a site to
an adequate one is adequate.

The hypothesis on the source is linear adequacy rather than adequacy because 06V0 lifts only
along a map of finite free module extensions; for a general adequate source the presenting
modules are arbitrary and no such lifting is available. -/
public theorem isAdequate_kernel_of_isLinearlyAdequate_site (A : Type u) [CommRing A]
    (hA : (Spec (CommRingCat.of A)).size < κ)
    {F G : ModuleValuedFunctorOn.{max u w, u}
      (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ))}
    (ψ : F ⟶ G)
    (hF : IsLinearlyAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) F)
    (hG : IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) G) :
    IsAdequate (siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)) (kernel ψ) := by
  let ι := siteAlgebraInclusion.{u, u} A (schemeSizeBelow κ)
  let b : BaseAlgebraObject.{u} ι := BaseAlgebraObject.siteOfSpecMem (schemeSizeBelow κ) hA
  let E := moduleExtensionFunctorOn.{max u w, u} ι
  obtain ⟨n, m, fa, ⟨eF₀⟩⟩ := hF
  obtain ⟨M₂, N₂, bb, ⟨eG₀⟩⟩ := hG
  let a₀ : finiteFreeModule.{max u w} A n ⟶ finiteFreeModule.{max u w} A m :=
    moduleHomOfExtensionNatTransOn.{max u w} b fa
  have hfa : fa = E.map a₀ := moduleExtension_natTransOn_eq_map.{max u w} b fa
  let αF : F ≅ kernel (E.map a₀) :=
    (presheafOfModulesUliftIso.{u, max u w} (algebraRingDiagramOn ι) F).symm ≪≫ eF₀ ≪≫
      kernelIsoOfEq hfa
  let αG : G ≅ kernel (E.map bb) :=
    (presheafOfModulesUliftIso.{u, max u w} (algebraRingDiagramOn ι) G).symm ≪≫ eG₀
  let ψ' : kernel (E.map a₀) ⟶ kernel (E.map bb) := αF.inv ≫ ψ ≫ αG.hom
  have hd : kernel.ι (E.map a₀) ≫ E.map a₀ = 0 := kernel.condition _
  have hexact : (CategoryTheory.ShortComplex.mk (kernel.ι (E.map a₀)) (E.map a₀) hd).Exact :=
    CategoryTheory.ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (E.map a₀))
  obtain ⟨χ, hχ⟩ := exists_lift_from_finite_free_kernel_site hκ hsl A
    (M := (M₂ : Type (max u w))) hA n m (kernel (E.map a₀)) (kernel.ι (E.map a₀)) (E.map a₀)
    (ψ' ≫ kernel.ι (E.map bb)) hd hexact
  let t : finiteFreeModule.{max u w} A n ⟶ M₂ := moduleHomOfExtensionNatTransOn.{max u w} b χ
  have hχ' : χ = E.map t := moduleExtension_natTransOn_eq_map.{max u w} b χ
  have hsq : kernel.ι (E.map a₀) ≫ E.map t = ψ' ≫ kernel.ι (E.map bb) := by
    rwa [← hχ']
  exact (isAdequate_kernel_of_moduleExtensionLift.{max u w} ι a₀ bb t hsq).of_iso
    (kernel.mapIso ψ ψ' αF αG (by simp [ψ']))

end AdequateFunctor

end
