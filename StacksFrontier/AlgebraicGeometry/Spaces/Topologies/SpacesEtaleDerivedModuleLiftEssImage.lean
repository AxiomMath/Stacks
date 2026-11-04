module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEssImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimitsCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedModuleLiftFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts

/-!
# The essential image of the derived transport to the spaces-étale site

Let `X` be an algebraic space over a scheme `S` and let
`ι : D(𝒪_{X_étale}) ⥤ D(𝒪_{X_{spaces,étale}})` be the derived transport
`AlgebraicGeometry.Space.toSpacesEtaleDerivedModules`, which raises the universe of the module
sections from `u` to `u + 1`. This file proves that an object `K` of `D(𝒪_{X_{spaces,étale}})`
whose cohomology sheaves are the transports of quasi-coherent `𝒪_{X_étale}`-modules is `ιL` for
some `L ∈ D_QCoh(𝒪_{X_étale})`.

The argument is `CategoryTheory.Functor.mem_essImage_mapDerivedCategory_of_exists_isKInjective`:
bounded objects lift by induction on their amplitude using that `ι` is full on morphisms into
`D_QCoh` (`AlgebraicGeometry.Space.bijective_toSpacesEtaleDerivedModules_map`), bounded below ones
as homotopy colimits of their truncations, and arbitrary ones as derived limits of their
truncations `τ_{≥ -n} K`, whose cohomology on `X_étale` is computed by Stacks 0D3E (1).

## Main results

* `AlgebraicGeometry.Space.exists_toSpacesEtaleDerivedModules_obj_iso`: **the essential image of
  `ι` on objects with cohomology the transports of quasi-coherent modules.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategoryB

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale site, which is
-- not a `SmallCategory`; at low priority the standard model chooses nothing where a global one
-- exists. The spaces-étale model is passed explicitly.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- Every complex of `𝒪_{X_étale}`-modules with quasi-coherent cohomology has a K-injective
resolution which `ι` carries to a K-injective complex. -/
theorem exists_quasiIso_isKInjective_toSpacesEtaleModules
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hK : QcohDerived B S hS X (DerivedCategory.Q.obj K)) :
    ∃ (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (γ : K ⟶ I), QuasiIso γ ∧
      I.IsKInjective ∧ CochainComplex.IsKInjective
        (((toSpacesEtaleModules B S hS X).mapHomologicalComplex (.up ℤ)).obj I) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have hconv : Stacks.KInjectiveTower.TruncGEConvergent (DerivedCategory.Q.obj K) :=
    fun L c p δ hL hc ↦
      isIso_of_isDerivedLimit_truncGETower_unconditional B S hS X.1 X.2 _ hK L c p δ hL hc
  exact Stacks.KInjectiveTower.exists_quasiIso_isKInjective_map_isKInjective
    (toSpacesEtaleModules B S hS X) K hconv

/-- The transport `toSpacesEtaleModules` of `𝒪_{X_étale}`-modules to the spaces-étale site
preserves limits indexed by `ℕ`. -/
instance : PreservesLimitsOfShape (Discrete ℕ) (toSpacesEtaleModules B S hS X) :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse))

/-- The transport `toSpacesEtaleModules` of `𝒪_{X_étale}`-modules to the spaces-étale site
preserves colimits indexed by `ℕ`. -/
instance : PreservesColimitsOfShape (Discrete ℕ) (toSpacesEtaleModules B S hS X) :=
  haveI : PreservesColimitsOfShape (Discrete ℕ) (smallEtaleModuleULift B S hS X) :=
    haveI := Stacks.SheafOfModules.preservesColimitsOfShape_moduleULift
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (ULift.{u} ℕ)
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  inferInstanceAs (PreservesColimitsOfShape (Discrete ℕ) (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse))

/-- **The essential image of the derived transport to the spaces-étale site.** An object `K` of
`D(𝒪_{X_{spaces,étale}})` each of whose cohomology sheaves is the transport `ιM` of a
quasi-coherent `𝒪_{X_étale}`-module `M` is isomorphic to `ιL` for some `L ∈ D_QCoh(𝒪_{X_étale})`.
-/
theorem exists_toSpacesEtaleDerivedModules_obj_iso
    (K : @DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) _ _
      (spacesEtaleHasDerivedCategory B S hS X))
    (hK : @derivedCategoryB _ _ _ (spacesEtaleHasDerivedCategory B S hS X)
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).map
          (toSpacesEtaleModules B S hS X)) K) :
    ∃ L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X L ∧
      Nonempty ((toSpacesEtaleDerivedModules B S hS X).obj L ≅ K) := by
  let := spacesEtaleHasDerivedCategory B S hS X
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasProductsOfShape_nat_modules_ringUniverse B S hS X.1 X.2
  have := hasProductsOfShape_nat_derivedCategory_modules B S hS X.1 X.2
  have : HasProductsOfShape ℕ (@DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) _ _
      (spacesEtaleHasDerivedCategory B S hS X)) :=
    Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{_, u + 1, u + 1,
      u + 1, u + 1} _
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :=
    SheafOfModules.DifferentialGradedModule.hasExactColimitsOfShape_nat _
  have hC : HasExactCountableDirectSums (Modules.{u, u} B S hS X.1 X.2) :=
    hasExactCountableDirectSums_of_isGrothendieckAbelian.{u} _
  have hD : HasExactCountableDirectSums (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :=
    hasExactCountableDirectSums_of_isGrothendieckAbelian.{u + 1} _
  obtain ⟨L, ⟨e⟩⟩ :=
    (toSpacesEtaleModules B S hS X).mem_essImage_mapDerivedCategory_of_exists_isKInjective
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (exists_quasiIso_isKInjective_toSpacesEtaleModules B S hS X)
      (fun G hP hsurj L p δ hT q N htrans ↦ by
        obtain ⟨p', ⟨δ', hT'⟩, τ, hτ, ⟨hl⟩⟩ := isLimit_cohomology_of_isDerivedLimit_of_epi
          B S hS X.1 X.2 G (fun n q ↦ hP n q) hsurj L ⟨p, δ, hT⟩ q
        exact DerivedCategory.isIso_homologyFunctor_map_comp_π_of_isLimit G p p' δ δ' hT hT' q τ
          hτ hl N htrans)
      hC hD K hK
  exact ⟨L, (toSpacesEtaleModules B S hS X).derivedCategoryB_of_mapDerivedCategory_obj_iso
    _ e hK, ⟨e⟩⟩

end AlgebraicGeometry.Space

end
