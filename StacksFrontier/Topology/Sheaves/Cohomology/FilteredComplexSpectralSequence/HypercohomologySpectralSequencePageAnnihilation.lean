module

public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologyAnnihilation
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequence

/-!
# Annihilation of the second page of the hypercohomology spectral sequence

Let `(X, 𝒪_X)` be a ringed space, let `K` be an object of the derived category of
`𝒪_X`-modules and let `r ∈ Γ(X, 𝒪_X)`. The second page of the hypercohomology spectral sequence
of `K` in bidegree `(p, j)` is `H^p(X, H^j(K))`, so if `r` kills the cohomology sheaf `H^j(K)`
then it annihilates that term.

Both halves of this are already available and only the composition is new:
`Stacks.Cohomology.FilteredComplex.hypercohomologySpectralSequence_e₂` identifies the term with
the degree-`p` cohomology of the derived global sections of `H^j(K)` placed in degree zero, and
`Stacks.Cohomology.FilteredComplex.mem_annihilator_homology_RΓ_single_of_center_app_eq_zero`
annihilates exactly that module. The derived global-sections functor the identification uses is
the one carried by the canonical truncation datum of the spectral sequence, together with its
comparison map and its right-derived-functor property, which is what the annihilation statement
asks for.

Multiplication by `r` enters as an element `η` of the centre of the category of module sheaves
together with the hypothesis that it acts on global sections by `r`, and the hypothesis on `K` is
the vanishing `η.app (H^j(K)) = 0`; on a ringed space
`Stacks.SheafOfModules.terminalSectionToEnd` is that element and
`Stacks.SheafOfModules.terminalSectionToEnd_app_eq_zero` turns a section-level annihilation of
`H^j(K)` into that vanishing.

## Main results

* `Stacks.Cohomology.FilteredComplex.mem_annihilator_hypercohomologySpectralSequence_page_two`:
  **a global function killing the cohomology sheaf `H^j(K)` annihilates the second-page term
  `E_2^{p, j} = H^p(X, H^j(K))`** of the hypercohomology spectral sequence of `K`.

## References

* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

/-- **A global function killing a cohomology sheaf of `K` annihilates the corresponding row of
the second page of the hypercohomology spectral sequence of `K`.** If the central endomorphism
`η`, which acts on global sections by `r ∈ Γ(X, 𝒪_X)`, is the zero endomorphism of the cohomology
sheaf `H^j(K)`, then `r` annihilates `E_2^{p, j} = H^p(X, H^j(K))` for every `p`.

This is the second of the two hypotheses on the spectral sequence that the construction of the
filtration of [Stacks, Tag 0GA1] out of it asks for: there `K = Lp^*M̃(q)` on the blowup and the
vanishing of `η` on `H^j(K)` comes from the section-level annihilation of [Stacks, Tag 0GA0]. -/
theorem mem_annihilator_hypercohomologySpectralSequence_page_two (X : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (η : CatCenter (SheafOfModules.{u} (structureSheafRing X)))
    (r : (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
    (hη : ∀ (M : SheafOfModules.{u} (structureSheafRing X)) (x : M.val.obj (op ⊤)),
      (η.app M).val.app (op ⊤) x = r • x)
    (p j : ℤ)
    (hK : η.app ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) j).obj K) = 0) :
    r ∈ Module.annihilator ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))
      (((hypercohomologySpectralSequence X K).spectralSequence.page 2).X (p, j)) := by
  have := (hypercohomologySpectralSequence X K).truncation.isRightDerived
  obtain ⟨e₂⟩ := hypercohomologySpectralSequence_e₂ X K p j
  rw [e₂.toLinearEquiv.annihilator_eq]
  exact mem_annihilator_homology_RΓ_single_of_center_app_eq_zero X
    (hypercohomologySpectralSequence X K).truncation.RΓ
    (hypercohomologySpectralSequence X K).truncation.α η r hη _ hK p

end Stacks.Cohomology.FilteredComplex

end
