module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalFunctionsPseudoCoherentWhole
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.ReflectionAlongTriangulatedFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompleteShift
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# Tag 0CQI at an affine open, compatibly with the completion units

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `U ⊂ X` an
affine open, with `A = Γ(X, U)` and `I = ℐ(U)`. [Stacks, Tag 0CQI] identifies

`RΓ(U, K^∧) ≅ RΓ(U, K)^∧`   in `D(A)`,

and `Stacks.Algebraization.nonempty_iso_derivedSections_derivedCompletion_affine` proves it, for
every object `K` of `D(𝒪_X)`. That isomorphism is a `Nonempty`: it comes from identifying two
derived limits of one tower, and a derived limit is determined only up to a non-canonical
isomorphism. This file upgrades it to an isomorphism **compatible with the two completion
units**,

`η_{RΓ(U, K)} ≫ ε = RΓ(U, η_K)`,

which is what a statement about the *image* of a unit — the density that part (2) of
[Stacks, Tag 0A0K] needs over an affine open — can be transported across.

## How

The display, quantified over every object, already implies the compatible form: that is the
content of
`CategoryTheory.ObjectProperty.isoReflectionMap_of_nonempty_iso`, the triangulated-functor
engine of `Completion/ReflectionAlongTriangulatedFunctor.lean`. Applying it needs three things of
`RΓ(U, -)` and nothing of `K`:

* it is triangulated, being the unbounded right derived functor of evaluation at `U` on a
  Grothendieck abelian category with enough K-injectives;
* the derived-complete objects of `D(𝒪_X)` along `ℐ` are stable under the shift
  (`AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj`), and so are those of `D(A)`
  along `I` (`Stacks.Algebraization.isDerivedComplete_shift`);
* derived completeness over `A` is invariant under isomorphism
  (`DerivedCompleteRecurrence.isDerivedComplete_of_iso`), which is what produces the analogue of
  [Stacks, Tag 099J] — that `RΓ(U, K^∧)` is derived complete — out of the display rather than
  assuming it.

The source proves [Stacks, Tag 0CQI] by applying [Stacks, Tag 0A0G] to the morphism of ringed
topoi `(𝒞, 𝒪) ⟶ (pt, A)`, and that route is unavailable here — there is no morphism of ringed
sites from a general ringed site to the ringed point, as the module documentation of
`DerivedCompletionRinged/GlobalSectionsCompletion.lean` records. The engine replaces it: the
argument it runs is the one `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/PushforwardCommutesCompletionCanonical.lean` runs for `Rf_*`, at the
generality of a triangulated functor.

## Main results

* `Stacks.Algebraization.exists_iso_derivedSections_derivedCompletion_affine_unit` — the
  unit-compatible form of [Stacks, Tag 0CQI] at an affine open.

## References

* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (opensRingedSite)
open Stacks.Cohomology.HypercohomologyEdge (derivedSections derivedSectionsUnit homotopySections)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData) (U : X.affineOpens)
  (K : DerivedCategory X.Modules)

/-- **[Stacks, Tag 0CQI] at an affine open of a locally Noetherian scheme, compatibly with the
completion units.** With `A = Γ(X, U)` and `I = ℐ(U)`, there is an isomorphism

`ε : RΓ(U, K)^∧ ≅ RΓ(U, K^∧)`

with `η_{RΓ(U, K)} ≫ ε = RΓ(U, η_K)`, for every reflector onto the derived-complete objects of
`D(A)`.

`Stacks.Algebraization.nonempty_iso_derivedSections_derivedCompletion_affine` gives the two
objects abstractly isomorphic, for every object of `D(𝒪_X)`; that, plus the triangulatedness of
`RΓ(U, -)` and the shift stability of the two classes of derived-complete objects, is exactly the
input of `CategoryTheory.ObjectProperty.isoReflectionMap_of_nonempty_iso`. See the module
documentation. -/
public theorem exists_iso_derivedSections_derivedCompletion_affine_unit :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) :=
      fun L ↦ IsDerivedComplete (𝓘.ideal U) L
    ∀ (C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤ P.FullSubcategory) (adj : C ⊣ P.ι),
      ∃ ε : (C ⋙ P.ι).obj ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) ≅
          (derivedSections (structureSheafRing X.toRingedSpace) U.1).obj
            ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).obj K),
        adj.unit.app ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) ≫ ε.hom =
          (derivedSections (structureSheafRing X.toRingedSpace) U.1).map
            ((AlgebraicGeometry.RingedSite.derivedCompletionUnit (opensRingedSite X.sheaf)
              (idealSheafSiteSubmodule 𝓘)).app K) := by
  intro P C adj
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- everything is spelled at the ringed site, where the completion functor lives; the two
  -- spellings of the structure sheaf of rings agree by `rfl`
  set O := Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O
  -- with more than one `HasDerivedCategory` instance ambient, synthesis of the shift-additivity
  -- `∀ n, (shiftFunctor (DerivedCategory C) n).Additive` fails; it is supplied by name, with the
  -- value search would have produced
  have hCa : ∀ n : ℤ, (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) n).Additive :=
    fun n => DerivedCategory.instAdditiveShiftFunctorInt n
  have hDa : ∀ n : ℤ, (shiftFunctor (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) n).Additive :=
    fun n => DerivedCategory.instAdditiveShiftFunctorInt n
  let hcs := Functor.IsRightDerivedFunctor.commShift (derivedSections O U.1)
    (derivedSectionsUnit O U.1)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) ℤ
  have hct : (derivedSections O U.1).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.Cohomology.Localization.enoughKInjectives (homotopySections O U.1)
      (derivedSections O U.1) (derivedSectionsUnit O U.1)
  have : ObjectProperty.IsStableUnderShift
      (AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u} (opensRingedSite X.sheaf)
        (idealSheafSiteSubmodule 𝓘)) ℤ :=
    ⟨fun n => ⟨fun _ hL =>
      AlgebraicGeometry.RingedSite.isDerivedComplete_shiftFunctor_obj _ _ n hL⟩⟩
  have : P.IsStableUnderShift ℤ :=
    ⟨fun n => ⟨fun _ hL => isDerivedComplete_shift (𝓘.ideal U) hL n⟩⟩
  exact ⟨_, ObjectProperty.unit_comp_isoReflectionMap_hom
    (AlgebraicGeometry.RingedSite.IsDerivedComplete.{u, u, u, u} (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule 𝓘)) P
    (AlgebraicGeometry.RingedSite.derivedCompletionAdjunction (opensRingedSite X.sheaf)
      (idealSheafSiteSubmodule 𝓘)) adj (derivedSections O U.1) (hCa := hCa) (hDa := hDa)
    (hFs := hcs) (hFt := hct)
    (fun e h => DerivedCompleteRecurrence.isDerivedComplete_of_iso e h)
    (fun E => ⟨(nonempty_iso_derivedSections_derivedCompletion_affine 𝓘 E U C adj).some.symm⟩)
    K⟩

end Stacks.Algebraization

end
