module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGenerationUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZeroUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# A constructible sheaf of modules is a quotient of finitely many extensions by zero

Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring. Every
constructible sheaf `ℱ` of `Λ`-modules on `X_étale` is a quotient of a finite direct sum
`⨁ᵢ jᵢ! Λ̲` of extensions by zero of the constant sheaf `Λ̲` along étale morphisms
`jᵢ : Wᵢ ⟶ X` with affine source. This is the first half of Stacks 095N (the finite generation
step of its proof), stated here for sheaves of `Λ`-modules on Mathlib's small étale sites,
`Stacks.EtaleCohomology.EtaleModules`.

## Main results

All in the namespace `Stacks.EtaleCohomology`.

* `exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule` — the epimorphism
  `⨁ᵢ jᵢ! Λ̲ ⟶ ℱ`.

## Implementation notes

The statement is transported from the small étale site of Tag 021B of the big étale site
`AlgebraicGeometry.BigEtaleSite.containing X`, where it is
`AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`, the generators
being `AlgebraicGeometry.moduleShriekConstant`. Constructibility is read in that big étale site
by `Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf`. The
equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sheaf categories preserves
coproducts and epimorphisms, carries extension by zero to extension by zero
(`AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIsoUnconditional`) and constant sheaves
to constant sheaves (`Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso`); the
rank-one module `ULift Λ` of the generators is identified with `Λ` by `ULift.moduleEquiv`.

The ring lives in `Type (u + 1)` for schemes in `Scheme.{u}`, so that `ModuleCat.of Λ Λ` is an
object of the coefficient category `ModuleCat.{u + 1} Λ` of `EtaleModules Λ X`.

## References

* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **A constructible sheaf of `Λ`-modules is a quotient of finitely many extensions by zero of
the constant sheaf**, the finite generation step of Stacks 095N. Let `X` be quasi-compact and
quasi-separated and `Λ` Noetherian. For a constructible sheaf `ℱ` of `Λ`-modules on `X_étale`
there are finitely many étale morphisms `eᵢ : Wᵢ ⟶ X` with `Wᵢ` affine and an epimorphism
`⨁ᵢ eᵢ! Λ̲ ⟶ ℱ`. -/
theorem exists_epi_sigma_etaleModuleExtensionByZero_of_isConstructibleEtaleModule
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : EtaleModules.{u, u + 1} Λ X)
    (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (W : Fin n → Scheme.{u}) (e : ∀ i, W i ⟶ X) (_ : ∀ i, Etale (e i))
      (_ : ∀ i, IsAffine (W i))
      (p : (∐ fun i ↦ (etaleModuleExtensionByZero.{u, u + 1} Λ (e i)).obj
        ((constantSheaf (W i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ))) ⟶ F), Epi p := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let Xb : B.Scheme := B.obj X hX
  have : CompactSpace Xb.1 := ‹CompactSpace X›
  have : QuasiSeparatedSpace Xb.1 := ‹QuasiSeparatedSpace X›
  let A := ModuleCat.{u + 1} Λ
  let eX := SmallEtale.sheafEquiv B X hX A
  let G := (etaleModuleToBoundedSite Λ B hX).obj F
  have hG : IsConstructibleModuleSheaf B Xb Λ G :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX F).1 hF
  obtain ⟨n, V, hV, f, hf⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_affine B Xb Λ (𝟙 G) hG
  rw [Category.comp_id] at hf
  refine ⟨n, fun i ↦ (V i).obj.left.1, fun i ↦ B.inclusion.map (V i).obj.hom,
    fun i ↦ (V i).property, fun i ↦ hV i, ?_⟩
  have c : ∀ i, (etaleModuleExtensionByZero.{u, u + 1} Λ (B.inclusion.map (V i).obj.hom)).obj
      ((constantSheaf (V i).obj.left.1.smallEtaleTopology A).obj (ModuleCat.of Λ Λ)) ≅
        eX.functor.obj (moduleShriekConstant.{u, u + 1, u + 1} B Xb Λ (V i)) := by
    intro i
    let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B Xb Λ
    let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B (V i).obj.left Λ
    let eW := SmallEtale.sheafEquiv B (V i).obj.left.1 (V i).obj.left.property A
    let T := SmallEtale.sheafEquivExtensionByZeroIsoUnconditional B X hX (V i) A
      (etaleModuleExtensionByZeroAdj.{u, u + 1} Λ (B.inclusion.map (V i).obj.hom))
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtalePostcompose B X hX (V i)) A
        (SmallEtale.topology B (V i).obj.left.1 (V i).obj.left.property)
        (SmallEtale.topology B X hX))
    let r := (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      (SmallEtale.topology B (V i).obj.left.1 (V i).obj.left.property)
      (V i).obj.left.1.smallEtaleTopology
      (SmallEtale.toEtaleSite B (V i).obj.left.1 (V i).obj.left.property) A).app
        (ModuleCat.of Λ Λ)
    let d : eW.functor.obj ((constantSheaf (SmallEtale.topology B (V i).obj.left.1
          (V i).obj.left.property) A).obj (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≅
        (constantSheaf (V i).obj.left.1.smallEtaleTopology A).obj (ModuleCat.of Λ Λ) :=
      eW.functor.mapIso ((constantSheaf _ A).mapIso
          (ULift.moduleEquiv : ULift.{u + 1} Λ ≃ₗ[Λ] Λ).toModuleIso ≪≫ r.symm) ≪≫
        eW.counitIso.app _
    exact (etaleModuleExtensionByZero.{u, u + 1} Λ _).mapIso d.symm ≪≫ T.app _
  refine ⟨(Sigma.mapIso c).hom ≫ (PreservesCoproduct.iso eX.functor _).inv ≫
    eX.functor.map f ≫ eX.counitIso.hom.app F, ?_⟩
  have : Epi (eX.functor.map f) :=
    have : eX.functor.IsLeftAdjoint := eX.toAdjunction.isLeftAdjoint
    (Functor.preservesEpimorphisms_of_isLeftAdjoint eX.functor).preserves f
  exact epi_comp' inferInstance (epi_comp' inferInstance (epi_comp' this inferInstance))

end Stacks.EtaleCohomology

end
