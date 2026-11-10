module
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierProperCurves.KernelSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeShortExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparisonUnconditional

/-!
# The Artin–Schreier sequence pushed forward

Let `f : X ⟶ S` be a morphism of schemes over `𝐅_p`. Applying the unbounded derived direct image
`Rf_*` to the Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` of [Stacks, Tag 0A3J] on
`X_étale` gives a long exact sequence, from which this file reads off `Rᵠf_*(𝐙/p𝐙)` in terms of
the higher direct images `Rᵠf_*𝐆_a` and of the map `F - 1` on them. This is the first half of case
(b) of the proof of [Stacks, Tag 0GKV].

## Main results

* `Stacks.ArtinSchreier.isIso_additiveDirectImageComparison`: `𝐆_{a,S} ⟶ f_*𝐆_{a,X}` is an
  isomorphism when `Γ(V, 𝒪_V) ⟶ Γ(X ×_S V, 𝒪)` is bijective for every étale `V ⟶ S`.
* `Stacks.ArtinSchreier.artinSchreierMap_comp_additiveDirectImageComparison_unconditional`:
  that comparison intertwines the two Artin–Schreier maps.
* `Stacks.ArtinSchreier.etaleAbelianDerivedDirectImageSingleHomologyIso`: `Hⁿ(Rf_*(K[0]))` is
  the classical higher direct image `Rⁿf_* K`, naturally in `K`.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ArtinSchreier

/-- **`𝒪_Y ⟶ g_*𝒪_X` invertible makes `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` bijective**: on global sections
the unit map is the map on global functions. -/
theorem bijective_appTop_of_isIso_unitToPushforwardUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsIso (Scheme.Modules.unitToPushforwardUnit g)] : Function.Bijective g.appTop := by
  have h₁ : Function.Bijective ((Scheme.Modules.unitToPushforwardUnit g).app ⊤) :=
    ConcreteCategory.bijective_of_isIso _
  have h₂ : Function.Bijective ((Scheme.unitModule X).presheaf.map
      (eqToHom (show (⊤ : X.Opens) = g ⁻¹ᵁ ⊤ by simp)).op) :=
    ConcreteCategory.bijective_of_isIso _
  have : (g.appTop : Γ(Y, ⊤) → Γ(X, ⊤)) = (Scheme.unitModule X).presheaf.map
      (eqToHom (show (⊤ : X.Opens) = g ⁻¹ᵁ ⊤ by simp)).op ∘
        (Scheme.Modules.unitToPushforwardUnit g).app ⊤ :=
    funext fun y => (unitToPushforwardUnit_app_top g y).symm
  rw [this]
  exact h₂.comp h₁

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`𝐆_{a,S} ⟶ f_*𝐆_{a,X}` is an isomorphism** as soon as, for every étale `V ⟶ S`, pulling
back global functions along `X ×_S V ⟶ V` is bijective: on sections over `V` the comparison is
that pullback. -/
theorem isIso_additiveDirectImageComparison
    (h : ∀ V : S.Etale, Function.Bijective (pullback.fst V.hom f).appTop) :
    IsIso (additiveDirectImageComparisonGeneral.{u, v} f) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  have : ((additiveDirectImageComparisonGeneral.{u, v} f).hom.app V : _ → _) =
      ofSection.{u, v} ∘ (pullback.fst V.unop.hom f).appTop ∘ ULift.down := by
    funext x
    obtain ⟨x, rfl⟩ := ofSection_surjective x
    rfl
  change Function.Bijective ((additiveDirectImageComparisonGeneral.{u, v} f).hom.app V : _ → _)
  rw [this]
  have hof : Function.Bijective (ofSection.{u, v} (U := (smallEtaleBaseChange f).obj V.unop)) :=
    ⟨ofSection_injective, ofSection_surjective⟩
  have hdown : Function.Bijective (ULift.down : ULift.{max (u + 1) v} Γ(V.unop.left, ⊤) → _) :=
    ⟨ULift.down_injective, ULift.down_surjective⟩
  exact hof.comp ((h V.unop).comp hdown)

variable {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (hX : (p : Γ(X, ⊤)) = 0)

include hS in
/-- **The direct-image comparison intertwines the Artin–Schreier maps**, the Frobenius being
compatible with pulling back functions. -/
theorem artinSchreierMap_comp_additiveDirectImageComparison_unconditional :
    artinSchreierMap.{u, v} S hp hS ≫ additiveDirectImageComparisonGeneral.{u, v} f =
      additiveDirectImageComparisonGeneral.{u, v} f ≫
        (etaleAbelianDirectImage.{u, v} f).map (artinSchreierMap.{u, v} X hp hX) := by
  simp only [artinSchreierMap, Preadditive.sub_comp, Preadditive.comp_sub, Functor.map_sub,
    Category.id_comp,
    frobeniusMap_comp_additiveDirectImageComparison_general f hp hS hX]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **`Hⁿ(Rf_*(K[0]))` is the classical higher direct image `Rⁿf_* K`**, naturally in the abelian
sheaf `K`: `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the unbounded
derived direct image of abelian sheaves. -/
def etaleAbelianDerivedDirectImageSingleHomologyIso (n : ℕ) :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) 0 ⋙
        etaleAbelianDerivedDirectImage.{u, v} f ⋙
          DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v}) (n : ℤ) ≅
      (etaleAbelianDirectImage.{u, v} f).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived _ _
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective n

end Stacks.ArtinSchreier
