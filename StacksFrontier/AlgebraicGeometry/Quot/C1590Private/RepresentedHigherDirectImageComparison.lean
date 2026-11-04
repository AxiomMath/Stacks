module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonSituation

/-!
# Higher direct images along a morphism of represented algebraic spaces

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` whose underlying morphism of schemes
`φ` is quasi-compact and separated, and let `𝓕` be a quasi-coherent `𝒪_{T'}`-module. Write `h_g`
for the morphism of algebraic spaces `yoneda.map g` and `𝓕^a` for the module on the small étale
site of `h_{T'}` associated with `𝓕`. This file proves

`R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a`

for every `k`: Stacks 071N read in the spaces formalism, the input `h071N` of
`StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus`.

## The proof

The small étale site of `h_U` is the small étale site of the scheme underlying `U`, with the same
structure sheaf, so the modules on the two sites are identified by the equivalence
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`; across it the direct image
along `h_g` is the direct image along the morphism of small étale ringed sites of `φ`
(`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`). Right derived functors are
transported along equivalences of abelian categories
(`CategoryTheory.Functor.rightDerivedObjIsoOfEquivalence`), so `R ᵏ (h_g)_* (𝓕^a)` is the
transport of `R ᵏ φ_{small,*} (𝓕^a)`, which is `(R ᵏ φ_* 𝓕)^a` by the étale clause of Stacks 071N
for schemes (`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso`).

## Main results

* `AlgebraicGeometry.C1590Private.nonempty_rightDerived_modulePushforward_representedSpaceMap_iso`:
  `R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a` for `φ` quasi-compact and separated.

## Implementation notes

No `stacks` attribute is placed: 071N is registered on the scheme-level statement, and this is its
transport to represented algebraic spaces, stated with exactly the hypotheses (quasi-compact and
separated) of the input `h071N` it discharges. The scheme-level comparison needs only
quasi-separatedness, which separatedness implies.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.C1590Private

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 071N for a quasi-compact separated morphism, in the spaces formalism.** Let
`g : T' ⟶ T` be a morphism of the big fppf site over `S` whose underlying morphism of schemes `φ`
is quasi-compact and separated, and let `𝓕` be a quasi-coherent `𝒪_{T'}`-module. Then for every
`k`

`R ᵏ (h_g)_* (𝓕^a) ≅ (R ᵏ φ_* 𝓕)^a`,

where `h_g = yoneda.map g` and `(-)^a` is the associated module on the small étale site of the
represented algebraic space. -/
theorem nonempty_rightDerived_modulePushforward_representedSpaceMap_iso
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map g))
    (hsep : IsSeparated ((BigFppfOver.toScheme B S hS).map g))
    (F : ((BigFppfOver.toScheme B S hS).obj T').Modules) (hF : F.IsQuasicoherent)
    (k : ℕ) :
    have := Space.hasInjectiveResolutions_modules B S hS (yoneda.obj T')
      (isAlgebraicSpace_yoneda B S hS T')
    have := Space.modulePushforward_additive B S hS
      (Space.representedSpaceMap B S hS g)
    Nonempty (((Space.modulePushforward B S hS
        (Space.representedSpaceMap B S hS g)).rightDerived k).obj
        ((Space.representedAssociatedModule B S hS T'
          (isAlgebraicSpace_yoneda B S hS T')).obj F) ≅
      (Space.representedAssociatedModule B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).obj
        (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map g)).rightDerived
          k).obj F)) := by
  intro _ _
  have := hF
  have : QuasiCompact (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) := hqc
  have : QuasiSeparated (SmallEtale.schemeHom (associatedBigEtaleSite B) g.left) :=
    inferInstanceAs (QuasiSeparated ((BigFppfOver.toScheme B S hS).map g))
  have := Space.enoughInjectives_modules B S hS (yoneda.obj T')
    (isAlgebraicSpace_yoneda B S hS T')
  let eA : SheafOfModules.{u} (Space.representedSchemeStructureSheaf B S hS T') ≌
      Space.Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T') :=
    Space.representedSmallEtaleModuleEquivalence B S hS T'
  let eB : SheafOfModules.{u} (Space.representedSchemeStructureSheaf B S hS T) ≌
      Space.Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
    Space.representedSmallEtaleModuleEquivalence B S hS T
  have : eA.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : eB.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits
      (Space.modulePushforward B S hS (Space.representedSpaceMap B S hS g)) :=
    Space.preservesFiniteLimits_modulePushforward B S hS _
  let e₁ := Functor.rightDerivedObjIsoOfEquivalence
    (A' := Space.Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (B' := Space.Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) eA eB
    (SheafOfModules.pushforward.{u} (Space.representedSchemeStructureMapRing B S hS g))
    (Space.modulePushforward B S hS (Space.representedSpaceMap B S hS g))
    (Space.representedModulePushforwardSquareIso B S hS g
      (Space.relativelyRepresentable_yoneda_map B S hS g))
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).obj F) k
  let e₂ := _root_.AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleObjIso
    (associatedBigEtaleSite B) g.left F k
  exact ⟨e₁.symm ≪≫ eB.functor.mapIso e₂⟩

end AlgebraicGeometry.C1590Private

end
