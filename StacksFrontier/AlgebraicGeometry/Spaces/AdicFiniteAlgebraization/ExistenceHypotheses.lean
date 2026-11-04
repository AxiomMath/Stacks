module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.QuotientSystemAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistenceSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseIdealSubmoduleSheafComparison

/-!
# Grothendieck's existence theorem on algebraic spaces, uniformly in the space

The two halves of Grothendieck's existence theorem on an algebraic space `W` separated and of
finite type over a Noetherian ring `A` complete along `I`, along the ideal sheaf `I 𝒪_W`
(`AlgebraicGeometry.Space.baseIdealSheaf`), stated uniformly in `W` with the structure morphism
written as a morphism to the base object of the site:

* `AlgebraicGeometry.Space.ExistenceEssSurj`: essential surjectivity of the completion functor
  onto the coherent adic systems with proper support (Stacks 08BE);
* `AlgebraicGeometry.Space.ExistenceFullyFaithful`: its bijectivity on maps into a coherent module
  with proper support (Stacks 08B9).

## Main results

* `AlgebraicGeometry.Space.existenceEssSurj_holds`: `ExistenceEssSurj` holds when `A` is
  `I`-adically complete.
* `AlgebraicGeometry.Space.existenceFullyFaithful_holds`: `ExistenceFullyFaithful` holds when `A`
  is `I`-adically complete.

## References

* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- Grothendieck's existence theorem on an algebraic space `W` separated and of finite type over
`Spec A`: essential surjectivity of the completion functor along `I 𝒪_W` onto the coherent adic
systems with proper support (Stacks 08BE). -/
abbrev ExistenceEssSurj : Prop :=
  ∀ {W : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B (Spec (.of A)) hA W)
    (g : W ⟶ yoneda.obj (baseObject A B hA)), IsSeparated B (Spec (.of A)) hA g →
    ∀ hft : IsFiniteType B (Spec (.of A)) hA g,
      letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hW g hft.1
      (completionFunctorProperOver B (Spec (.of A)) hA W (yoneda.obj (baseObject A B hA)) hW
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) g hft.1
        (baseIdealSheaf A ⟨W, hW⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨W, hW⟩ I)).EssSurj

/-- Grothendieck's existence theorem on an algebraic space `W` separated and of finite type over
`Spec A`: full faithfulness of the completion functor on maps into a coherent module with proper
support (Stacks 08B9). -/
abbrev ExistenceFullyFaithful : Prop :=
  ∀ {W : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B (Spec (.of A)) hA W)
    (g : W ⟶ yoneda.obj (baseObject A B hA)), IsSeparated B (Spec (.of A)) hA g →
    ∀ hft : IsFiniteType B (Spec (.of A)) hA g,
    ∀ M N : CoherentModules.{u, u} B (Spec (.of A)) hA W hW,
      HasProperSupport B (Spec (.of A)) hA hW (isAlgebraicSpace_yoneda B _ hA _) g hft.1
        ((SheafOfModules.toSheaf _).obj N.obj) →
      letI := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hW g hft.1
      Function.Bijective (fun a : M ⟶ N => (completionFunctor B (Spec (.of A)) hA W hW
        (baseIdealSheaf A ⟨W, hW⟩ I) (isQuasicoherentOnSite_baseIdealSheaf A ⟨W, hW⟩ I)).map a)

/-- **Grothendieck's existence theorem, essential surjectivity (Stacks 08BE)**, in the uniform form
`AlgebraicGeometry.Space.ExistenceEssSurj`. -/
theorem existenceEssSurj_holds [IsAdicComplete I A] : ExistenceEssSurj A I B hA := by
  intro W hW g hsep hft
  let := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hW g hft.1
  have h := isEquivalence_completionFunctorProperOver I ⟨W, hW⟩
    (ObjectProperty.homMk g : (⟨W, hW⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      schemeSpace (baseObject A B hA)) hft hsep
  have aux : ∀ (J : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA W hW).O))).Submodule)
      (hJ : J = baseIdealSheaf A ⟨W, hW⟩ I) (hJq : J.toSheafOfModules.IsQuasicoherentOnSite),
      (completionFunctorProperOver B (Spec (.of A)) hA W (yoneda.obj (baseObject A B hA)) hW
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) g hft.1 J hJq).EssSurj →
      (completionFunctorProperOver B (Spec (.of A)) hA W (yoneda.obj (baseObject A B hA)) hW
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) g hft.1
        (baseIdealSheaf A ⟨W, hW⟩ I)
        (isQuasicoherentOnSite_baseIdealSheaf A ⟨W, hW⟩ I)).EssSurj := by
    rintro J rfl hJq hes
    exact hes
  exact aux _ (baseIdealSubmodule_eq_baseIdealSheaf ⟨W, hW⟩ I)
    (C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := W) (hX := hW) I)
    (@Functor.IsEquivalence.essSurj _ _ _ _ _ h)

/-- **Grothendieck's existence theorem, full faithfulness (Stacks 08B9)**, in the uniform form
`AlgebraicGeometry.Space.ExistenceFullyFaithful`. -/
theorem existenceFullyFaithful_holds [IsAdicComplete I A] : ExistenceFullyFaithful A I B hA := by
  intro W hW g hsep hft M N hN
  have hg : g = (isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from W :=
    (isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _
  subst hg
  exact bijective_completionFunctor_map_of_hasProperSupport ⟨W, hW⟩ I hft hsep M N hN

end AlgebraicGeometry.Space

end
