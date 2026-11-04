module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# Extension by zero of a derived direct image, by excision

Let `e : U ⟶ X` be an open immersion with closed complement `i : ∂ ⟶ X`, `v : V ⟶ X` an open
immersion whose image contains `∂`, and `j' : U₀ ⟶ U`, `e' : U₀ ⟶ V` the two sides of the
cartesian square `U₀ = U ×_X V`. For a sheaf `F` of `Λ`-modules on `U₀`,

`e_! (R j'_* F) ≅ R v_* (e'_! F)` in `D⁺(X_étale, Λ)`.

Write `N = R v_*(e'_! F)`. Its restriction to `U` is `R j'_* F` by base change along the open
immersion `e` (`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion`),
and its restriction to `∂` vanishes: `∂ ⟶ X` factors through `V`, the restriction of `R v_*` to
`V` is the identity (base change along `v` itself), and the restriction of `e'_! F` to
`∂ ⊆ V ∖ U₀` is zero. The triangle `e_! e⁻¹ N ⟶ N ⟶ i_* i⁻¹ N` of [Stacks, Tag 0GKL] then
identifies `e_! e⁻¹ N` with `N`.

This is the excision step in the computation of `H²_c` of `R j'_* F` on an affine curve with a
nonempty finite set of points removed from every component: there `X` is a compactification of
`U` and `V = X ∖ (U ∖ U₀)`.

## Main results

* `Stacks.EtaleCohomology.nonempty_etaleModuleDerivedExtensionByZero_derivedDirectImage_iso`.

## Implementation notes

The statement is made in the standard model `HasDerivedCategory.standard` of the derived
categories, in which the derived functors used are defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe u

namespace Stacks.EtaleCohomology

open Stacks.DerivedFunctor

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- **The restriction of `R v_*` to the open `V` is the identity**, on `D⁺(V_étale, Λ)`: base
change along `v` itself, and the identifications of `(𝟙 V)⁻¹` and `R(𝟙 V)_*` with the
identity. -/
theorem nonempty_etaleModuleDerivedInverseImagePlus_derivedDirectImage_iso_self
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (G : DerivedCategory.Plus (EtaleModules.{u, 0} Λ V)) :
    Nonempty ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ v).obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ v).obj G) ≅ G) := by
  have sq : IsPullback (𝟙 V) (𝟙 V) v v := IsKernelPair.id_of_mono v
  have hbc := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ v sq G
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} Λ (𝟙 V)) :=
    preservesFiniteLimits_of_natIso (etaleModuleDirectImageIdIso Λ V).symm
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ (𝟙 V)) :=
    preservesFiniteColimits_of_natIso (etaleModuleDirectImageIdIso Λ V).symm
  exact ⟨asIso ((etaleModuleDerivedBaseChange.{u, 0} Λ v (𝟙 V) v (𝟙 V) sq.w.symm).app G) ≪≫
    (exactMapDerivedCategoryPlusIso (etaleModuleDirectImage.{u, 0} Λ (𝟙 V))).symm.app _ ≪≫
    (mapDerivedCategoryPlusNatIso (etaleModuleDirectImageIdIso Λ V)).app _ ≪≫
    (Functor.mapDerivedCategoryPlusIdIso).app _ ≪≫
    (mapDerivedCategoryPlusNatIso (etaleModuleInverseImageIdIso.{u, 0} Λ V)).app G ≪≫
    (Functor.mapDerivedCategoryPlusIdIso).app G⟩

/-- **Excision for the extension by zero of a derived direct image.** Let `e : U ⟶ X` be an open
immersion with closed complement `i : ∂ ⟶ X`, `v : V ⟶ X` an open immersion and `c : ∂ ⟶ V` with
`c ≫ v = i`, and `U₀ = U ×_X V` with projections `j' : U₀ ⟶ U` and `e' : U₀ ⟶ V`, the image of
`e'` being the complement of that of `c`. For a sheaf `F` of `Λ`-modules on `U₀`,
`e_!(R j'_* F) ≅ R v_*(e'_! F)`. -/
theorem nonempty_etaleModuleDerivedExtensionByZero_derivedDirectImage_iso
    {X U U₀ V D : Scheme.{u}} (e : U ⟶ X) [IsOpenImmersion e] (i : D ⟶ X) [IsClosedImmersion i]
    (hei : Set.range e.base = (Set.range i.base)ᶜ) (v : V ⟶ X) [IsOpenImmersion v] (c : D ⟶ V)
    (hc : c ≫ v = i) (e' : U₀ ⟶ V) [IsOpenImmersion e'] (j' : U₀ ⟶ U) [IsOpenImmersion j']
    (sq : IsPullback e' j' v e) (hce : Set.range e'.base = (Set.range c.base)ᶜ)
    (F : EtaleModules.{u, 0} Λ U₀) :
    Nonempty ((etaleModuleDerivedExtensionByZero.{u, 0} Λ e).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ j').obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≅
      (etaleModuleDerivedDirectImage.{u, 0} Λ v).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ e').obj F))) := by
  set G := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ V) 0).obj
    ((etaleModuleExtensionByZero.{u, 0} Λ e').obj F)
  set N := (etaleModuleDerivedDirectImage.{u, 0} Λ v).obj G
  -- the restriction of `N` to `U` is `R j'_* F`
  have hbc := isIso_etaleModuleDerivedBaseChange_of_isOpenImmersion Λ v sq G
  let eF : (etaleModuleInverseImage.{u, 0} Λ e').obj
      ((etaleModuleExtensionByZero.{u, 0} Λ e').obj F) ≅ F :=
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ e').app _ ≪≫
      (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ e').unit.app F)).symm
  let KU := (etaleModuleRestriction.{u, 0} Λ e).mapDerivedCategoryPlus.obj N
  let eU : KU ≅ (etaleModuleDerivedDirectImage.{u, 0} Λ j').obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
    (mapDerivedCategoryPlusNatIso (etaleModuleInverseImageRestrictionIso.{u, 0} Λ e)).symm.app N ≪≫
      asIso ((etaleModuleDerivedBaseChange.{u, 0} Λ v j' e e' sq.w.symm).app G) ≪≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ j').mapIso
        ((etaleModuleInverseImage.{u, 0} Λ e').mapDerivedCategoryPlusObjSingleIso _ ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)
  -- the restriction of `N` to `∂` vanishes
  let KZ := (etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryPlus.obj N
  have hKZ : IsZero KZ := by
    obtain ⟨eV⟩ := nonempty_etaleModuleDerivedInverseImagePlus_derivedDirectImage_iso_self Λ v G
    have hz : IsZero ((etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlus.obj G) :=
      ((DerivedCategory.Plus.singleFunctor _ 0).map_isZero
        (isZero_etaleModuleInverseImage_extensionByZero Λ c e' hce F)).of_iso
        ((etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusObjSingleIso _)
    exact hz.of_iso (eqToIso (congrArg
        (fun m => (etaleModuleInverseImage.{u, 0} Λ m).mapDerivedCategoryPlus.obj N) hc.symm) ≪≫
      (mapDerivedCategoryPlusNatIso (etaleModuleInverseImageCompIso.{u, 0} Λ c v)).app N ≪≫
      (mapDerivedCategoryPlusCompIso (etaleModuleInverseImage.{u, 0} Λ v)
        (etaleModuleInverseImage.{u, 0} Λ c)).symm.app N ≪≫
      (etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlus.mapIso eV)
  -- the triangle `e_! e⁻¹ N ⟶ N ⟶ i_* i⁻¹ N`
  obtain ⟨δ, hδ⟩ := exists_distTriang_etaleModuleExtensionByZero_directImage Λ i e hei
    (DerivedCategory.Plus.ι.obj N)
  obtain ⟨a₀, b₀, c₀, h₀⟩ := DerivedCategory.Plus.exists_distinguished_of_ι_objIso _ hδ
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ e).obj KU) N
    ((etaleModuleDerivedDirectImage.{u, 0} Λ i).obj KZ)
    (DerivedCategory.Plus.ι.mapIso
        ((exactMapDerivedCategoryPlusIso (etaleModuleExtensionByZero.{u, 0} Λ e)).symm.app KU) ≪≫
      (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app
        (DerivedCategory.Plus.ι.obj N))
    (Iso.refl _)
    (DerivedCategory.Plus.ι.mapIso
        ((exactMapDerivedCategoryPlusIso (etaleModuleDirectImage.{u, 0} Λ i)).symm.app KZ) ≪≫
      (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm.app
        (DerivedCategory.Plus.ι.obj N))
  have : IsIso a₀ := (Triangle.isZero₃_iff_isIso₁ _ h₀).1
    ((etaleModuleDerivedDirectImage.{u, 0} Λ i).map_isZero hKZ)
  exact ⟨(etaleModuleDerivedExtensionByZero.{u, 0} Λ e).mapIso eU.symm ≪≫ asIso a₀⟩

end Stacks.EtaleCohomology

end
