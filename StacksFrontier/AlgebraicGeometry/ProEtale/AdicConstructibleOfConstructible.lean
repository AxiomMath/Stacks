module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AdicLisseOfLocallyConstant
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedInverseImageComplete

/-!
# Constructible complexes on a Noetherian scheme are adic constructible

Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. Every object `K` of
`D_cons(X, Λ)` is adic constructible (Stacks 09C7): every affine open `U` of `X` has a
decomposition into constructible locally closed subschemes `U_j` such that `K|_{U_j}` is adic
lisse.

The cohomology sheaves of `K ⊗_Λ^L \underline{Λ/I}` are constructible and only finitely many are
nonzero, so one decomposition of `U` with connected strata trivializes all of them
(`exists_stratification_connectedSpace_isFiniteTypeLocallyConstant_homology`;
a Noetherian scheme is locally connected). On each stratum `U_j` the restriction `K|_{U_j}` is
constructible (`AlgebraicGeometry.ProEtale.isConstructibleDerivedSheaf_derivedInverseImage`) and
the cohomology sheaves of its reduction, the restrictions of those of `K ⊗_Λ^L \underline{Λ/I}`,
are locally constant, so `K|_{U_j}` is adic lisse by Stacks 09C6.

## Main results

* `AlgebraicGeometry.ProEtale.isAdicConstructibleDerivedSheaf_of_isConstructibleDerivedSheaf`:
  Stacks 09C7.

## References

* [Stacks Project, Tag 09C7](https://stacks.math.columbia.edu/tag/09C7)
* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 09C7.** Let `X` be a Noetherian scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an
ideal. Every object `K` of `D_cons(X, Λ)` is adic constructible. -/
@[stacks 09C7]
theorem isAdicConstructibleDerivedSheaf_of_isConstructibleDerivedSheaf {X : Scheme.{u}}
    [IsNoetherian X] {Λ : Type (max (u + 1) w)} [CommRing Λ] [IsNoetherianRing Λ] {I : Ideal Λ}
    {K : DerivedSheaves.{u, max (u + 1) w, w} X Λ}
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K) :
    IsAdicConstructibleViaDerivedInverseImage.{u, max (u + 1) w, w} X Λ I K := fun U => by
  obtain ⟨s, hsc, hs⟩ :=
    exists_stratification_connectedSpace_isFiniteTypeLocallyConstant_homology hK U
  refine ⟨s, fun j => ?_⟩
  have := hsc j
  have := s.isImmersion j
  refine isAdicLisseDerivedSheaf_of_isLocallyConstant
    (isConstructibleDerivedSheaf_derivedInverseImage X (s.inclusion j) I hK fun i => hs i j)
    fun i => ?_
  obtain ⟨e⟩ := nonempty_homology_derivedReduction_derivedInverseImage_iso (s.inclusion j) Λ I K i
  exact Stacks.ConstantSheaf.isLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf
    (ObjectProperty.prop_of_iso _ e.symm (hs i j))

end AlgebraicGeometry.ProEtale

end
