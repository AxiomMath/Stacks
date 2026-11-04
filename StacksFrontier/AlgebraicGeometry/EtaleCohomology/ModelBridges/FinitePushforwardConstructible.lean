module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image along a finite morphism of finite presentation, on the site of Tag 021B

Let `p : T ⟶ S` be a morphism of a big étale site `B` which is finite and of finite presentation,
and let `Λ` be a Noetherian ring. [Stacks, Tag 095R] says that the direct image `p_*ℱ` of a
constructible sheaf of `Λ`-modules `ℱ` on `T_étale` is constructible. The library proves it in the
model `Stacks.EtaleCohomology.EtaleModules` of Mathlib's small étale site,
`Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite`. This file
reads it on the small étale sites of Tag 021B cut out of `B`, where the direct image is
`AlgebraicGeometry.BigEtaleSite.smallPushforward`.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_smallPushforward_of_isFinite` —
  **Stacks 095R** for sheaves of modules on the small étale sites of Tag 021B.

## Implementation notes

Nothing is re-proved. A sheaf `ℱ` on the site of Tag 021B of `T` is, up to the unit of the
equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`, the transport
`Stacks.EtaleCohomology.etaleModuleToBoundedSite` of its image `ℱ'` on Mathlib's small étale site;
constructibility of `ℱ'` may be read in `B` by
`Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf`, and the two
direct images correspond under the transports by
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`.

The coefficient ring lives in `Type (u + 1)` and the sheaves of modules in `ModuleCat.{u + 1}`,
the universes of the library's Tag 095R in the model `EtaleModules`.

## References

* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S) (Λ : Type (u + 1)) [CommRing Λ]
  [IsNoetherianRing Λ]

/-- **Stacks 095R for sheaves of modules over a Noetherian ring, on the site of Tag 021B.** Let
`p : T ⟶ S` be a finite morphism of finite presentation of a big étale site, let `Λ` be a
Noetherian ring and let `ℱ` be a constructible sheaf of `Λ`-modules on `T_étale`. Then `p_*ℱ` is a
constructible sheaf of `Λ`-modules on `S_étale`.

This is `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite`,
transported from Mathlib's small étale sites along the equivalences
`AlgebraicGeometry.SmallEtale.sheafEquiv`, under which the two direct images correspond
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`). -/
@[sga "4 IX 2.14" "(i), A-module variant", sga "5 I 1.14" "b)"]
public theorem isConstructibleModuleSheaf_smallPushforward_of_isFinite
    [IsFinite (B.inclusion.map p)] (hfp : FinitePresentation (B.inclusion.map p))
    (F : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B T Λ F) :
    IsConstructibleModuleSheaf B S Λ ((B.smallPushforward p (ModuleCat.{u + 1} Λ)).obj F) := by
  let eT := SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{u + 1} Λ)
  let eS := SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{u + 1} Λ)
  let F' : EtaleModules.{u, u + 1} Λ T.obj := eT.functor.obj F
  have hF' : IsConstructibleEtaleModule Λ F' := by
    rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B T.property]
    exact isConstructibleModuleSheaf_congr B Λ T (eT.unitIso.app F) hF
  have h := isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite Λ (B.inclusion.map p)
    hfp F' hF'
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf.{u, u + 1} Λ B S.property] at h
  refine isConstructibleModuleSheaf_congr B Λ S
    ((SmallEtale.toEtaleSitePushforwardBaseChangeIso B p (ModuleCat.{u + 1} Λ)).app F' ≪≫
      (B.smallPushforward p (ModuleCat.{u + 1} Λ)).mapIso (eT.unitIso.app F).symm) h

end AlgebraicGeometry

end
