module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Serre vanishing for the underlying abelian sheaf of a quasi-coherent module

Let `X` be a scheme, `M` a quasi-coherent `𝒪_X`-module and `V ⊆ X` an affine open. Serre vanishing
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` ([Stacks, Tag 01XB]) says that the
cohomology `Hᵖ(V, M)` computed in `Mod(𝒪_X)` vanishes for `p > 0`. This file records the same
vanishing for the cohomology of the *underlying abelian sheaf* of `M`, computed in the category of
abelian sheaves on `X`, at the universe `u` of the scheme and after the universe lift to
`AddCommGrpCat.{u + 1}`:

`Hᵖ(V, M) = 0` in `Ab(X_Zar)` and in `Ab(X_Zar)` at `u + 1`, for `p > 0`.

The passage from modules to abelian sheaves is [Stacks, Tag 01F1] part (1),
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso`; the passage between the
universes is `CategoryTheory.Functor.rightDerivedIsoOfSquare` for the universe lift of abelian
sheaves, which is exact and preserves injective objects.

## Main results

Everything lives in the namespace `Stacks.Cohomology.Cech`.

* `preservesInjectiveObjects_uliftSheafFunctor_zariski`: the universe lift `u ⟶ u + 1` of abelian
  sheaves on the Zariski site of a scheme preserves injective objects.
* `isZero_rightDerived_sheafSections_toSheaf_of_isAffineOpen`: Serre vanishing for the underlying
  abelian sheaf of a quasi-coherent module, at the universe `u`.
* `isZero_rightDerived_sheafSections_uliftToSheaf_of_isAffineOpen`: the same after the universe
  lift to `AddCommGrpCat.{u + 1}`.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Sheaves.UniverseLift

universe u

namespace Stacks.Cohomology.Cech

variable (X : Scheme.{u})

/-- Abelian sheaves on the Zariski site of a scheme admit sheafification at the coefficient
universe `u + 1`. -/
local instance : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- Abelian sheaves on the Zariski site of a scheme, valued in `AddCommGrpCat.{u + 1}`, form a
Grothendieck abelian category; in particular they have enough injectives. -/
local instance : IsGrothendieckAbelian.{u + 1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :=
  have : EssentiallySmall.{u + 1} X.Opens := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- **The universe lift `u ⟶ u + 1` of abelian sheaves on the Zariski site of a scheme preserves
injective objects.** -/
instance preservesInjectiveObjects_uliftSheafFunctor_zariski :
    (uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X)).PreservesInjectiveObjects :=
  have : HasSeparator (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasSeparator.{u}
  preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _

/-- **Serre vanishing for the underlying abelian sheaf of a quasi-coherent module.** For a
quasi-coherent `𝒪_X`-module `M` and an affine open `V`, the higher right derived functors of
`Γ(V, -)` on abelian sheaves vanish at the underlying abelian sheaf of `M`. -/
theorem isZero_rightDerived_sheafSections_toSheaf_of_isAffineOpen (M : X.Modules)
    [M.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op V)).rightDerived p).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) :=
  (Functor.map_isZero (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat.{u})
      ((ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup X.ringCatSheaf V p M).2
        (isZero_hgroup_of_isAffineOpen X M V hV p hp))).of_iso
    ((ModuleComparison.rightDerivedSectionsForgetIso X.ringCatSheaf V p).app M).symm

/-- **Serre vanishing for the underlying abelian sheaf of a quasi-coherent module, after the
universe lift.** For a quasi-coherent `𝒪_X`-module `M` and an affine open `V`, the higher right
derived functors of `Γ(V, -)` on abelian sheaves valued in `AddCommGrpCat.{u + 1}` vanish at the
universe lift of the underlying abelian sheaf of `M`. -/
theorem isZero_rightDerived_sheafSections_uliftToSheaf_of_isAffineOpen (M : X.Modules)
    [M.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}).obj
      (op V)).rightDerived p).obj ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) :=
  have : (uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Functor.map_isZero AddCommGrpCat.uliftFunctor.{u + 1, u}
      (isZero_rightDerived_sheafSections_toSheaf_of_isAffineOpen X M V hV p hp)).of_iso
    ((Functor.rightDerivedIsoOfSquare (uliftSheafFunctor.{u + 1, u} (Opens.grothendieckTopology X))
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op V))
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}).obj (op V))
      AddCommGrpCat.uliftFunctor.{u + 1, u}
      (sheafSectionsULiftIso.{u + 1, u} (Opens.grothendieckTopology X) V) p).app
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).symm

end Stacks.Cohomology.Cech
