module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeCalculus
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# The edge morphism of an exact functor is the comparison of Stacks 015Z

For additive `P : ℬ ⥤ 𝒜` preserving injective objects and additive `Q : 𝒜 ⥤ ℰ`, two comparisons
between `P ⋙ Qⁿ` and `(P ⋙ Q)ⁿ` are available in this library when `P` is in addition exact:

* `Stacks.Cohomology.RightDerivedEdge.edge`, the edge morphism of the Grothendieck spectral
  sequence of the pair, which is defined with *no* exactness hypothesis on `P` and is invertible
  under one (`Stacks.Cohomology.RightDerivedEdge.isIso_edge_app`);
* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, Stacks 015Z, which is an
  isomorphism by construction.

The first is the inverse of the second.

## Main results

* `Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app` — **the edge
  morphism of an exact functor preserving injectives is the inverse of the comparison of Stacks
  015Z.**

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/


@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedEdge

attribute [local implicit_reducible] Stacks.Cohomology.CompositeRightDerived.mapInjRes

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
  {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ] [HasInjectiveResolutions ℬ]
  {ℰ : Type u₃} [Category.{v₃} ℰ] [Abelian ℰ]
  (P : ℬ ⥤ 𝒜) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [P.PreservesInjectiveObjects] (Q : 𝒜 ⥤ ℰ) [Q.Additive]

/-- **The edge morphism of an exact functor preserving injectives is the inverse of the comparison
of Stacks 015Z.** For such a `P`, the component at `X` of
`Stacks.Cohomology.RightDerivedEdge.edge P Q n` is the component at `X` of the inverse of
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n`. -/
theorem edge_app_eq_compRightDerivedNatIso_inv_app (n : ℕ) (X : ℬ) :
    (edge P Q n).app X =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso P Q n).inv.app X := by
  have h0 : (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).ι.f 0 ≫
      HomologicalComplex.Hom.f (𝟙 (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).cocomplex) 0 =
      P.map ((injectiveResolution X).ι.f 0) := by
    rw [HomologicalComplex.id_f, Category.comp_id]
    dsimp [Stacks.Cohomology.CompositeRightDerived.mapInjRes]
    simp
  refine (cancel_epi ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
    P Q n).hom.app X)).mp ?_
  rw [Iso.hom_inv_id_app,
    edge_app_eq P Q n (injectiveResolution X)
      (Stacks.Cohomology.CompositeRightDerived.mapInjRes P (injectiveResolution X))
      (𝟙 (Stacks.Cohomology.CompositeRightDerived.mapInjRes P
        (injectiveResolution X)).cocomplex) h0,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app P Q n X]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (congrArg (fun z => ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).hom ≫ z)
      (Category.id_comp ((injectiveResolution X).isoRightDerivedObj (P ⋙ Q) n).inv)).trans
    (Iso.hom_inv_id _)

end Stacks.Cohomology.RightDerivedEdge

end
