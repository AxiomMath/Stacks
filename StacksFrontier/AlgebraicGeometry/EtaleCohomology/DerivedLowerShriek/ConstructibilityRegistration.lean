module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.RelativeCurveGeneric
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ProperSmoothCurveNoetherian
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension

/-!
# Stacks 0GKX: `Rf_! M̲` is constructible for a smooth affine relative curve

Let `S` be a Noetherian scheme, `f : X ⟶ S` separated, affine and smooth of relative dimension
`1`, `Λ` a torsion Noetherian ring and `M` a finite `Λ`-module. Then `Rf_! M̲` has constructible
cohomology sheaves. The proof is
`Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_of_fiberDimension_le_one`,
with Stacks 0GKV over a Noetherian base
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`).

The statements are made in the standard model of the derived category
(`HasDerivedCategory.standard`), in which `Rf_!` is stated.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_homology_derivedLowerShriek_constantSheaf`:
  Stacks 0GKX.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [-instance] hasSheafifyEtale

attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- Stacks 0GKV over a Noetherian base
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian`), in
the form of the hypothesis `h0GKV` of the constructibility results. -/
local macro "h0GKV%" : term =>
  `(fun _ _ f _ _ _ hdim _ ℓ _ q =>
    isConstructibleEtaleModule_rightDerivedConstantUnit_of_isNoetherian _ f hdim ℓ q)


/-- **Stacks 0GKX.** Let `S` be a Noetherian scheme of `B`, `f : X ⟶ S` a separated, affine,
smooth morphism of relative dimension `1`, `j` a compactification of `f` (through which
`Rf_! = Rf̄_* ∘ j_!`), `Λ` a Noetherian ring which is torsion (`m = 0` in `Λ` for some `m > 0`),
and `M` a finite `Λ`-module. Then every cohomology sheaf of `Rf_! M̲` is constructible. The source
also assumes `S` affine of finite dimension, which is not needed. -/
@[stacks 0GKX "S Noetherian (affine and finite-dimensional not needed); Rf_! through any \
compactification j of f; Λ torsion as m = 0 in Λ for some m > 0"]
theorem isConstructibleEtaleModule_homology_derivedLowerShriek_constantSheaf
    (B : BigEtaleSite.{u}) (S : B.Scheme) [IsNoetherian S.obj] {X : Scheme.{u}}
    (f : X ⟶ S.obj) [IsSeparated f] [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (Λ : Type) [CommRing Λ] [IsNoetherianRing Λ]
    (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0) (M : ModuleCat.{u + 1} Λ) (hM : Module.Finite Λ M)
    (k : ℤ) :
    IsBigSiteConstructibleEtaleModule B S Λ ((DerivedCategory.Plus.homologyFunctor _ k).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : LocallyOfFinitePresentation f := inferInstance
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  have : QuasiCompact f := inferInstance
  exact isConstructibleEtaleModule_homology_derivedLowerShriek_of_fiberDimension_le_one B S f
    ⟨‹_›, ‹_›, ‹_›⟩
    (fun s => topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 f s) j Λ m hm hΛ M hM
    h0GKV% _ ⟨Iso.refl _⟩ k

end Stacks.EtaleCohomology

end
