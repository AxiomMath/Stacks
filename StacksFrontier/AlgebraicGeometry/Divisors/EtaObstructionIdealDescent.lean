module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.Homology.Eta.Perfect.TotalDirectSumIdeal

/-!
# The obstruction ideal depends only on the sheafified complex

Let `A` be a commutative ring and let `M^•`, `N^•` be bounded complexes of finite free
`A`-modules given in chosen bases.  More on Algebra, Tag 0GSW says that the degreewise
obstruction ideal `J_i(M^•, f) ⊆ A ⧸ fA` does not change when `M^•` is replaced by another
bounded complex of finite free modules isomorphic to it in `D(A)`.  This file states that
invariance for an isomorphism of the *sheafifications* on `Spec A` instead: two bounded
complexes whose associated complexes of `𝒪_{Spec A}`-modules become isomorphic in
`D(𝒪_{Spec A})` have the same obstruction ideals.

## Main results

* `AlgebraicGeometry.StandardModel.derivedIsoOfTildeDerivedIso`: an isomorphism of the
  sheafifications of two complexes of `A`-modules in `D(𝒪_{Spec A})` descends to an isomorphism
  in `D(A)`.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_tilde_derived_iso`: **the degreewise
  obstruction ideals of two bounded complexes with isomorphic sheafifications agree.**
* `Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal_eq_of_tilde_derived_iso`: hence so do
  the total obstruction ideals.
* `Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_tilde_derived_iso_unit_mul`: the same
  comparison when the two complexes are taken with equations differing by a unit.

## Implementation notes

The descent is full faithfulness of derived sheafification,
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`, together with
`CategoryTheory.Functor.mapDerivedCategoryFactors`, which identifies the derived functor on the
class of a complex with the class of the degreewise sheafification.  Derived sheafification is
fully faithful because the unit of the derived `Spec`–`Γ` adjunction is invertible, which is
Tag 06Z0.

The model of the derived category is pinned with `attribute [local instance 10000]
HasDerivedCategory.standard`, at that priority: the import closure makes `HasDerivedCategory` a
global instance for `ModuleCat A` and for `X.Modules`, which a default-priority local attribute
would not beat.

## References

* [Stacks Project, Tag 0GSW](https://stacks.math.columbia.edu/tag/0GSW)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.StandardModel

variable (R : CommRingCat.{u})

/-- **An isomorphism of sheafified complexes descends to the derived category of modules.**  If
the complexes of `𝒪_{Spec R}`-modules obtained by degreewise sheafification of two complexes
`K`, `L` of `R`-modules become isomorphic in `D(𝒪_{Spec R})`, then `K` and `L` are isomorphic in
`D(R)`.

Derived sheafification is fully faithful
(`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`) and computes the class of
the degreewise sheafification (`CategoryTheory.Functor.mapDerivedCategoryFactors`), so the given
isomorphism is the image of a unique isomorphism of `D(R)`. -/
def derivedIsoOfTildeDerivedIso (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
        DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L :=
  (mapDerivedCategoryFullyFaithful R).preimageIso
    ((tilde.functor R).mapDerivedCategoryFactors.app K ≪≫ e ≪≫
      ((tilde.functor R).mapDerivedCategoryFactors.app L).symm)

end AlgebraicGeometry.StandardModel

namespace Stacks.Decalage.DirectSumIdeal

variable (R : CommRingCat.{u})

/-- **The degreewise obstruction ideal depends only on the sheafified complex.**  Let `f ∈ A` be
a nonzerodivisor of `A = R` and let `M^•`, `N^•` be bounded complexes of finite free
`A`-modules whose determinantal ideals `I_i(M^•, f)` are principal for `M^•`.  If the
sheafifications of `M^•` and `N^•` become isomorphic in `D(𝒪_{Spec A})`, then
`J_i(M^•, f) = J_i(N^•, f)` for every `i`.

This is More on Algebra, Tag 0GSW —
`Stacks.Decalage.DirectSumIdeal.etaDirectSumIdeal_eq_of_derived_iso`, which asks for an isomorphism
in `D(A)` — fed with the descent `AlgebraicGeometry.StandardModel.derivedIsoOfTildeDerivedIso` of
the given isomorphism of sheaf complexes. -/
theorem etaDirectSumIdeal_eq_of_tilde_derived_iso (f : R) (hf : IsRegular f)
    (M N : BoundedComplex R) (hI : ∀ i : ℤ, (idealI M f i).IsPrincipal)
    (e : DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.toCochainComplex) ≅
        DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            N.toCochainComplex)) :
    ∀ i : ℤ, etaDirectSumIdeal M f i = etaDirectSumIdeal N f i :=
  etaDirectSumIdeal_eq_of_derived_iso f hf M N
    ⟨AlgebraicGeometry.StandardModel.derivedIsoOfTildeDerivedIso R
      M.toCochainComplex N.toCochainComplex e⟩ hI

/-- **The total obstruction ideal depends only on the sheafified complex.** -/
theorem etaTotalDirectSumIdeal_eq_of_tilde_derived_iso (f : R) (hf : IsRegular f)
    (M N : BoundedComplex R) (hI : ∀ i : ℤ, (idealI M f i).IsPrincipal)
    (e : DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.toCochainComplex) ≅
        DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            N.toCochainComplex)) :
    etaTotalDirectSumIdeal M f = etaTotalDirectSumIdeal N f :=
  iSup_congr (etaDirectSumIdeal_eq_of_tilde_derived_iso R f hf M N hI e)

/-- **Two bounded complexes with isomorphic sheafifications and equations differing by a unit
have the same obstruction ideals.**  Let `f ∈ A` be a nonzerodivisor of `A = R`, let `u ∈ A` be
a unit, and let `M^•`, `N^•` be bounded complexes of finite free `A`-modules whose
sheafifications become isomorphic in `D(𝒪_{Spec A})`, the determinantal ideals
`I_i(M^•, f)` being principal.  Then the degreewise obstruction ideal of `N^•` at the equation
`u·f` is that of `M^•` at `f`, read across the identification `A ⧸ u·fA ≃+* A ⧸ fA` of the two
quotients by one and the same ideal. -/
theorem etaDirectSumIdeal_eq_of_tilde_derived_iso_unit_mul (f : R) (hf : IsRegular f)
    (u : Rˣ) (M N : BoundedComplex R) (hI : ∀ i : ℤ, (idealI M f i).IsPrincipal)
    (e : DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.toCochainComplex) ≅
        DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            N.toCochainComplex)) (i : ℤ) :
    Ideal.map (quotEquivUnitMul f u : R ⧸ Ideal.span {(u : R) * f} →+* R ⧸ Ideal.span {f})
        (etaDirectSumIdeal N ((u : R) * f) i) = etaDirectSumIdeal M f i := by
  have hfu : IsRegular ((u : R) * f) := u.isUnit.isRegular.mul hf
  have hIu : ∀ j : ℤ, (idealI M ((u : R) * f) j).IsPrincipal := fun j =>
    (idealI_unit_mul_eq M f u j) ▸ hI j
  rw [← etaDirectSumIdeal_eq_of_tilde_derived_iso R ((u : R) * f) hfu M N hIu e i]
  exact map_etaDirectSumIdeal_unit_mul_eq M f hf hI u i

end Stacks.Decalage.DirectSumIdeal

end
