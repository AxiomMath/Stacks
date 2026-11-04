module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackScalars
public import StacksFrontier.AlgebraicGeometry.DeRham.ClosedImmersionPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections

/-!
# Pullback of de Rham cohomology along an isomorphism

For an isomorphism of schemes `ψ : X' ⟶ X` and a morphism `p : X ⟶ S`, the pullback
`ψ^* : H^i_dR(X/S) ⟶ H^i_dR(X'/S)` of Section 0FL6 is bijective: the canonical map of de Rham
complexes `Ω^•_{X/S} ⟶ ψ_*Ω^•_{X'/S}` is an isomorphism (`ψ` is étale), and so is the comparison
`ψ_* ⟶ Rψ_*` (`ψ` is a closed immersion).

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_deRhamCohomologyPullback_of_isIso`: on the abelian
  realization.
* `Stacks.DeRhamBaseChange.bijective_deRhamPullbackSquare_of_isIso`: on the module realization.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.LerayLowDegree (abelianPushforward)
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S : Scheme.{u}} (ψ : X' ⟶ X) [IsIso ψ] (p : X ⟶ S) (q : X' ⟶ S)
  (h : ψ ≫ p = q ≫ 𝟙 S)

/-- Along an isomorphism the canonical map of forms `Ω^n_{X/S} ⟶ ψ_*Ω^n_{X'/S}` is an
isomorphism. -/
instance isIso_deRhamFormsPushforwardHom_app (n : ℕ) :
    IsIso ((deRhamFormsPushforwardHom ψ p q (𝟙 S) h).app (n : ℤ)) := by
  have hmap : IsIso (relativeDifferentialFormsMap ψ p q (𝟙 S) h (n : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale ψ p q (𝟙 S) h (n : ℤ)
  have hu : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app
      (relativeDifferentialForms p (n : ℤ))) := inferInstance
  have h' : IsIso (Stacks.DeRhamBaseChange.formsAdjoint ψ q p (𝟙 S) h n) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hu (Functor.map_isIso (Scheme.Modules.pushforward ψ)
      (relativeDifferentialFormsMap ψ p q (𝟙 S) h (n : ℤ)))
  rw [← Stacks.DeRhamBaseChange.formsAdjoint_eq_deRhamFormsPushforwardHom ψ q p (𝟙 S) h n]
  exact h'

/-- Along an isomorphism the canonical map of de Rham complexes of abelian sheaves is an
isomorphism. -/
instance isIso_deRhamAbelianPushforwardMap : IsIso (deRhamAbelianPushforwardMap ψ p q (𝟙 S) h) :=
  @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _
    (deRhamAbelianPushforwardMap ψ p q (𝟙 S) h) fun n =>
    Functor.map_isIso (_root_.SheafOfModules.toSheaf _)
      ((deRhamFormsPushforwardHom ψ p q (𝟙 S) h).app (n : ℤ))

/-- Along an isomorphism the canonical map of de Rham complexes of abelian sheaves, as a map of
bounded-below cochain complexes, is an isomorphism. -/
instance isIso_deRhamAbelianPushforwardMapPlus :
    IsIso (deRhamAbelianPushforwardMapPlus ψ p q (𝟙 S) h) := by
  have : IsIso ((ComplexShape.embeddingUpNat.extendFunctor _).map
      (deRhamAbelianPushforwardMap ψ p q (𝟙 S) h) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} ψ.base) _ ComplexShape.embeddingUpNat).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_hom _)
  have : IsIso ((CochainComplex.plus _).ι.map (deRhamAbelianPushforwardMapPlus ψ p q (𝟙 S) h)) :=
    this
  exact isIso_of_fully_faithful (CochainComplex.plus _).ι _

/-- **Pullback of de Rham cohomology along an isomorphism over the identity is an isomorphism.** -/
instance isIso_deRhamCohomologyPullback_of_isIso (i : ℤ) :
    IsIso (deRhamCohomologyPullback ψ p q (𝟙 S) h i) := by
  unfold deRhamCohomologyPullback deRhamDerivedSectionsPullback
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRhamBaseChange

open _root_.AlgebraicGeometry

/-- **Along an isomorphism over the identity of the base, the pullback of de Rham cohomology is
bijective**, on the module realization. -/
theorem bijective_deRhamPullbackSquare_of_isIso {X X' S : Scheme.{u}} (g' : X' ⟶ X) [IsIso g']
    (f' : X' ⟶ S) (f : X ⟶ S) (w : g' ≫ f = f' ≫ 𝟙 S) (m : ℤ) :
    Function.Bijective (deRhamPullbackSquare g' f' f (𝟙 S) w m) := by
  unfold deRhamPullbackSquare
  exact ConcreteCategory.bijective_of_isIso _

end Stacks.DeRhamBaseChange
