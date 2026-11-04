module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedAtModel
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel

/-!
# `R ℰom(𝒪_Z, -)` read at two models of the derived category

`HasDerivedCategory.{w} C` is the assumption that a localization of `CochainComplex C ℤ` at the
quasi-isomorphisms has been *chosen*, so two choices give two categories `DerivedCategory C` and
a statement proved at one says nothing about the other. This library runs two choices side by
side: `CategoryTheory.HasDerivedCategory.standard`, installed file-locally, and the locally small
model of [Stacks, Tag 079Q], a global instance for sheaves of modules.

`Stacks.Duality.AnyModel.derivedSheafHomExactSupport`
is available at every model, its two derived categories being instance parameters. This file
compares two such readings, and carries across that comparison the one thing a consumer of
[Stacks, Tag 0A78] needs: membership in `D⁺_B`.

## Main definitions

* `StacksDraft.DerivedModel.modelCompQhIso` — the comparison equivalence of two models
  identifies the two localizations of the *homotopy* category.
* `StacksDraft.DerivedModel.modelSingleFunctorIso` — it identifies the two single-object
  functors `A ⥤ D(A)`.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.derivedSheafHomExactSupportModelIso` — `R ℰom(𝒪_Z, -)` taken at two models agree up to the
  comparison equivalences on source and target.

## Main results

* `StacksDraft.DerivedModel.isBoundedBelow_modelEquiv_functor_obj_iff` and
  `StacksDraft.DerivedModel.derivedCategoryBPlus_modelEquiv_functor_obj_iff` — boundedness below,
  and hence membership in `D⁺_B(A)`, is independent of the chosen model. The latter is the
  conjunction of the former with
  `StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff`.

## How the transport is obtained

`Stacks.Duality.AnyModel.derivedSheafHomExactSupport` is, at *every* model, the total right derived
functor of one and the same functor out of the homotopy category — sheaf Hom with exact support
followed by localization — with `derivedSheafHomExactSupportComparisonAtModel` of
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces` as its own total-derived unit.
So `StacksDraft.DerivedModel.rightDerivedModelIso` applies with no new input, and the two
comparisons it asks for are `StacksDraft.DerivedModel.modelCompQhIso` at `𝒪_X`-modules and at
`𝒪_Z`-modules. This is `StacksDraft.DerivedModel.derivedPushforwardModelIso` with `Rf_*` replaced
by `R ℰom(𝒪_Z, -)`, written in the same shape but for two arbitrary models rather than for the
shrinking comparison: `modelCompQhIso` is the arbitrary-model counterpart of
`StacksDraft.DerivedModel.shrinkComparisonQhIso` used there.

## Implementation notes

*Where these belong.* `modelCompQhIso` and the two boundedness transports are generic and would
sit beside `StacksDraft.DerivedModel.modelCompQIso` in
`StacksFrontier/Homology/DerivedCategory/ModelComparison.lean` and beside
`StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff` in
`StacksFrontier/Algebra/Homology/DerivedCategory/SerreSubcategoryModel.lean`. They are stated here
because those parts of the tree are being extended elsewhere; nothing below is specific to sheaf
Hom with exact support. The same displacement is why
`Dualizing.AnyModel.derivedHomModelIso` of
`StacksFrontier/RingTheory/Dualizing/DerivedHomModelComparison.lean` does not live next to
`derivedPushforwardModelIso` either.

*Models are named, never searched.* Importing
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean` brings the global locally
small instances into scope, so every `HasDerivedCategory` argument below is an explicit
parameter and none is left to instance search. This is the discipline that file's implementation
notes ask of its consumers.

*No `@[stacks]` attribute.* A comparison of two Lean choices of localization is an artefact of
formalizing the derived category, not a statement about two mathematical objects. The tags in
the chain are carried where they belong — [Stacks, Tag 079Q] by
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian` and [Stacks, Tag 0A76] by
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
`.derivedModulePushforwardSheafHomExactSupportAdjunctionAtModel`.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe w z v u

namespace StacksDraft.DerivedModel

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Cohomological boundedness below is independent of the chosen model.** The condition is the
vanishing of the cohomology objects in sufficiently negative degrees, and
`StacksDraft.DerivedModel.modelHomologyFunctorIso` identifies the cohomology of the two
models. -/
theorem isBoundedBelow_modelEquiv_functor_obj_iff (h₁ : HasDerivedCategory.{w} A)
    (h₂ : HasDerivedCategory.{z} A) (K : @DerivedCategory A _ _ h₁) :
    @DerivedCategoryB.IsBoundedBelow A _ _ h₂ ((modelEquiv h₁ h₂).functor.obj K) ↔
      @DerivedCategoryB.IsBoundedBelow A _ _ h₁ K :=
  exists_congr fun _ => forall_congr' fun n => imp_congr_right fun _ =>
    ⟨fun h => h.of_iso ((modelHomologyFunctorIso h₁ h₂ n).app K).symm,
      fun h => h.of_iso ((modelHomologyFunctorIso h₁ h₂ n).app K)⟩

/-- **Membership in `D⁺_B(A)` is independent of the chosen model.** An object of the derived
category at one model is cohomologically bounded below with cohomology in `B` exactly when its
transport to the other model is: the two halves are
`StacksDraft.DerivedModel.isBoundedBelow_modelEquiv_functor_obj_iff` and
`StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff`. -/
theorem derivedCategoryBPlus_modelEquiv_functor_obj_iff (B : ObjectProperty A)
    [B.IsClosedUnderIsomorphisms] (h₁ : HasDerivedCategory.{w} A)
    (h₂ : HasDerivedCategory.{z} A) (K : @DerivedCategory A _ _ h₁) :
    @DerivedCategoryB.derivedCategoryBPlus A _ _ h₂ B ((modelEquiv h₁ h₂).functor.obj K) ↔
      @DerivedCategoryB.derivedCategoryBPlus A _ _ h₁ B K :=
  and_congr (isBoundedBelow_modelEquiv_functor_obj_iff h₁ h₂ K)
    (derivedCategoryB_modelEquiv_functor_obj_iff B h₁ h₂ K)

end StacksDraft.DerivedModel

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open StacksDraft.DerivedModel

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})
    (hX₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X)))
    (hZ₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z)))
    (hX₂ : HasDerivedCategory.{z} (SheafOfModules.{u} (structureSheafRing S.X)))
    (hZ₂ : HasDerivedCategory.{z} (SheafOfModules.{u} (structureSheafRing S.Z)))

/-- **`R ℰom(𝒪_Z, -)` read at two models of the derived category.** The right derived functor of
sheaf Hom with exact support along a closed quotient morphism of ringed spaces, taken at one
choice of derived categories and taken at another, agree up to the comparison equivalences on
source and target. Both are total right derived functors of the same functor out of the homotopy
category, and a total right derived functor is unique up to a canonical isomorphism.

This is `StacksDraft.DerivedModel.derivedPushforwardModelIso` with `Rf_*` replaced by
`R ℰom(𝒪_Z, -)` and with the two models arbitrary rather than the standard and the locally small
one. -/
def derivedSheafHomExactSupportModelIso :
    @Stacks.Duality.AnyModel.derivedSheafHomExactSupport S hX₁ hZ₁ ⋙ (modelEquiv hZ₁ hZ₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙
        @Stacks.Duality.AnyModel.derivedSheafHomExactSupport S hX₂ hZ₂ :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
      (ComplexShape.up ℤ))
    (@derivedSheafHomExactSupportComparisonAtModel S hX₁ hZ₁)
    (@derivedSheafHomExactSupportComparisonAtModel S hX₂ hZ₂)
    (modelCompQhIso hX₁ hX₂)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (modelCompQhIso hZ₁ hZ₂))

/-- **Membership of `R ℰom(𝒪_Z, K)` in `D⁺_B` does not depend on the chosen model.** Taking the
right derived functor of sheaf Hom with exact support at one model and asking whether the result
is cohomologically bounded below with cohomology in `B` gives the same answer as taking it at
another model, the object `K` being transported by the comparison equivalence.

This is `derivedSheafHomExactSupportModelIso` read at `K`, followed by
`StacksDraft.DerivedModel.derivedCategoryBPlus_modelEquiv_functor_obj_iff`. It is what lets part
(1) of [Stacks, Tag 0A78] — proved at `CategoryTheory.HasDerivedCategory.standard`, where its
input part (1) of [Stacks, Tag 0A6H] lives — be read at any other model, in particular at the
locally small model of [Stacks, Tag 079Q], at which the right adjoint of [Stacks, Tag 0A9E] that
[Stacks, Tag 0A9X] compares against exists.

The `IsClosedUnderIsomorphisms` instance has to be supplied positionally by a consumer whose
property is spelled over `AlgebraicGeometry.Scheme.Modules Z` or
`SheafOfModules Z.ringCatSheaf`: the ambient category here is
`SheafOfModules.{u} (structureSheafRing S.Z)`, a third spelling of the same type, and instance
search does not cross between the three. -/
theorem derivedCategoryBPlus_derivedSheafHom_modelEquiv_iff
    (B : ObjectProperty (SheafOfModules.{u} (structureSheafRing S.Z)))
    [B.IsClosedUnderIsomorphisms] (K : @DerivedCategory _ _ _ hX₁) :
    @DerivedCategoryB.derivedCategoryBPlus _ _ _ hZ₂ B
        ((@Stacks.Duality.AnyModel.derivedSheafHomExactSupport S hX₂ hZ₂).obj
          ((modelEquiv hX₁ hX₂).functor.obj K)) ↔
      @DerivedCategoryB.derivedCategoryBPlus _ _ _ hZ₁ B
        ((@Stacks.Duality.AnyModel.derivedSheafHomExactSupport S hX₁ hZ₁).obj K) := by
  have e := (derivedSheafHomExactSupportModelIso S hX₁ hZ₁ hX₂ hZ₂).app K
  rw [← derivedCategoryBPlus_modelEquiv_functor_obj_iff B hZ₁ hZ₂]
  exact ⟨fun h => ⟨DerivedCategoryB.isBoundedBelow_of_iso e.symm h.1, fun n =>
      B.prop_of_iso ((@DerivedCategory.homologyFunctor _ _ _ hZ₂ n).mapIso e.symm) (h.2 n)⟩,
    fun h => ⟨DerivedCategoryB.isBoundedBelow_of_iso e h.1, fun n =>
      B.prop_of_iso ((@DerivedCategory.homologyFunctor _ _ _ hZ₂ n).mapIso e) (h.2 n)⟩⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
