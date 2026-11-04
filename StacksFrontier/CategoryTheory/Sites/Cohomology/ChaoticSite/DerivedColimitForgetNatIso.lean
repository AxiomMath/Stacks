module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitAcyclicVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitForgetComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LeftDerivedColimForget
public import StacksFrontier.Homology.Devissage.CompactGenerationOfDiagramsAnyModel
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryDirectSums

/-!
# Derived lower shriek at module coefficients, read on underlying abelian groups

Let `C` be a small category carrying the chaotic topology, let `B` be a ring and let `U_•` be a
cosimplicial object of `C` which is a point resolution, so that Tag 08Q9 computes `L_nπ_!` on both
diagrams of `B`-modules and abelian diagrams. Write `Ψ` for the functor applying `Mod(B) ⥤ Ab` to
the values of a diagram and `Φ` for `Mod(B) ⥤ Ab` itself. This file proves that the comparison

`Lπ_!(Ψ K) ⟶ Φ(Lπ_!(K))`

of `Stacks.ChaoticSite.derivedColimitForgetComparison` is an **isomorphism** for every object `K`
of the unbounded derived category `D(Cᵒᵖ ⥤ Mod(B))`. That identification is the `B`-module
structure which [Stacks, Tag 09CZ] puts on `Lπ_!(K)`.

## Main results

* `Stacks.ChaoticSite.isIso_diagramColimitForgetPost`: the underived comparison is invertible,
  the forgetful functor `Mod(B) ⥤ Ab` being a right adjoint.
* `Stacks.ChaoticSite.isZero_leftDerivedColim_diagramForget_of_projective`: `L_n colim` vanishes
  for `n > 0` on the underlying abelian diagram of a projective diagram of `B`-modules.
* `Stacks.ChaoticSite.isIso_derivedColimitForgetComparison_app_single_freeYoneda`: the comparison
  is invertible at a free diagram placed in degree zero.
* `Stacks.ChaoticSite.isIso_derivedColimitForgetComparison` and
  `Stacks.ChaoticSite.derivedColimitForgetComparisonNatIso`: the comparison is invertible
  everywhere, and the resulting identification.

## How the three inputs meet

`Stacks.ChaoticSite.derivedColimitForgetComparison_app_comp_counit` pins the comparison at an
object coming from the homotopy category: its right-hand side is a composite of three morphisms,
each invertible at a free diagram `CategoryTheory.Presheaf.freeYoneda X P` with `P` projective.

* The comparison of `Lπ_!` with `π_!` at the generator is invertible on diagrams of `B`-modules
  because the generator is projective, so its higher derived colimits vanish
  (`CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ`), and
  `Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_isZero_leftDerived` applies.
* On the **underlying abelian** diagram the generator is no longer projective — `B` need not be
  projective over `ℤ` — but the vanishing still holds, by
  `Stacks.ChaoticSite.leftDerivedColimForgetIso`, the module half of Tag 08Q9: `L_n colim` at
  module coefficients, forgotten to abelian groups, is `L_n colim` at abelian coefficients. This
  is the one place the point resolution is used.
* The underived comparison is invertible because the forgetful functor preserves the colimit over
  `Cᵒᵖ`, hence so is its degreewise action on complexes and the image of that under the two
  localizations.

`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` then carries the
invertibility from those generators to every object: both functors are exact and preserve direct
sums, the comparison is shift-compatible by
`Stacks.ChaoticSite.commShift_derivedColimitForgetComparison`, and the regular module is a
projective compact separator of `Mod(B)`.

## Implementation notes

`StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryDirectSums`, imported here for the
direct-sum preservation of a degreewise derived functor, also brings the global instance
`ModuleCat.hasDerivedCategory`, whose model has morphisms one universe lower than
`CategoryTheory.HasDerivedCategory.standard`. Everything in this development is seated at the
standard model, so that instance has to lose: `HasDerivedCategory.standard` is given priority
`2000`, as elsewhere in the repository.

## References

* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (C : Type u) [SmallCategory C] (B : Type u) [Ring B]

/-- The underived comparison is an isomorphism: the forgetful functor `Mod(B) ⥤ Ab` has a right
adjoint, so it preserves the colimit over `Cᵒᵖ`. -/
instance isIso_diagramColimitForgetPost : IsIso (diagramColimitForgetPost C B) := by
  have : ∀ F : Cᵒᵖ ⥤ ModuleCat.{u} B, IsIso ((diagramColimitForgetPost C B).app F) := fun F ↦
    inferInstanceAs (IsIso (colimit.post F (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})))
  exact NatIso.isIso_of_isIso_app _

/-- `L_n colim` vanishes for `n > 0` at a projective diagram of `B`-modules. -/
private theorem isZero_leftDerived_colim_of_projective (E : Cᵒᵖ ⥤ ModuleCat.{u} B) [Projective E]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived n).obj E) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Functor.isZero_leftDerived_obj_projective_succ _ m E

/-- `L_n colim` vanishes for `n > 0` on the underlying abelian diagram of a projective diagram of
`B`-modules: by `Stacks.ChaoticSite.leftDerivedColimForgetIso` it is the underlying abelian group
of `L_n colim` at the diagram of modules, and that vanishes at a projective object. -/
theorem isZero_leftDerivedColim_diagramForget_of_projective {U : CosimplicialObject C}
    (hU : IsPointResolution U) (E : Cᵒᵖ ⥤ ModuleCat.{u} B) [Projective E] (n : ℕ) (hn : 0 < n) :
    IsZero (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).obj
      ((forgetModuleDiagrams (C := C) (B := B)).obj E)) :=
  IsZero.of_iso
    ((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map_isZero
      (isZero_leftDerived_colim_of_projective C B E n hn))
    ((leftDerivedColimForgetIso (B := B) U hU n).app E).symm

/-- **The comparison is invertible at a free diagram placed in degree zero.** -/
theorem isIso_derivedColimitForgetComparison_app_single_freeYoneda
    {U : CosimplicialObject C} (hU : IsPointResolution U) (W : C) (P : ModuleCat.{u} B)
    [Projective P] :
    IsIso ((derivedColimitForgetComparison C B).app
      ((DerivedCategory.singleFunctor (Cᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
        (Presheaf.freeYoneda W P))) := by
  have hproj : Projective (Presheaf.freeYoneda W P) :=
    Stacks.CategoryHomology.freeYonedaProjective W P
  let X := (HomotopyCategory.quotient (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ)).obj
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj
      (Presheaf.freeYoneda W P))
  -- `Lπ_! = π_!` at the generator, on diagrams of modules: the generator is projective
  have hε₁ : IsIso ((totalDerivedColimitCounit C (ModuleCat.{u} B)).app X) :=
    isIso_totalDerivedColimitCounit_single_of_isZero_leftDerived (ModuleCat.{u} B)
      (Presheaf.freeYoneda W P) (isZero_leftDerived_colim_of_projective C B _)
  -- and on the underlying abelian diagrams: the higher derived colimits vanish there
  have hε₂0 : IsIso ((totalDerivedColimitCounit C AddCommGrpCat.{u}).app
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).obj
          ((forgetModuleDiagrams (C := C) (B := B)).obj (Presheaf.freeYoneda W P))))) :=
    isIso_totalDerivedColimitCounit_single_of_isZero_leftDerived AddCommGrpCat.{u}
      ((forgetModuleDiagrams (C := C) (B := B)).obj (Presheaf.freeYoneda W P))
      (isZero_leftDerivedColim_diagramForget_of_projective C B hU (Presheaf.freeYoneda W P))
  have hε₂ : IsIso ((totalDerivedColimitCounit C AddCommGrpCat.{u}).app
      (((forgetModuleDiagrams (C := C) (B := B)).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) :=
    (Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
        (totalDerivedColimitCounit C AddCommGrpCat.{u})).of_iso
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (forgetModuleDiagrams (C := C) (B := B))
            (ComplexShape.up ℤ) 0).app (Presheaf.freeYoneda W P)).symm) hε₂0
  -- the underived comparison is invertible
  have : IsIso ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
      (ComplexShape.up ℤ)).app X.as) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex
      (asIso (diagramColimitForgetPost C B)) (ComplexShape.up ℤ)).hom.app _))
  have : IsIso ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
        (ComplexShape.up ℤ)).app X.as)) := Functor.map_isIso _ _
  have hQ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient AddCommGrpCat.{u} (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (diagramColimitForgetPost C B)
          (ComplexShape.up ℤ)).app X.as))) := Functor.map_isIso _ _
  have hτ : IsIso ((derivedColimitForgetComparison C B).app (DerivedCategory.Qh.obj X)) := by
    refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ ?_ ?_
      (derivedColimitForgetComparison_app_comp_counit C B X)
    · exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance
    · exact IsIso.comp_isIso' (Functor.map_isIso _ _)
        (IsIso.comp_isIso' hε₂ hQ)
  exact (Stacks.DerivedCategoryComparisons.isIso_app_isClosedUnderIsomorphisms
      (derivedColimitForgetComparison C B)).of_iso
    ((DerivedCategory.singleFunctorIsoCompQh (Cᵒᵖ ⥤ ModuleCat.{u} B) 0).app
      (Presheaf.freeYoneda W P)).symm hτ

/-- **The comparison `Lπ_!(Ψ K) ⟶ Φ(Lπ_!(K))` is an isomorphism on the unbounded derived
category**, for a chaotic site admitting a cosimplicial point resolution. This is the dévissage
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` along the free diagrams on
the regular module, whose value at a generator is
`Stacks.ChaoticSite.isIso_derivedColimitForgetComparison_app_single_freeYoneda`. -/
theorem isIso_derivedColimitForgetComparison {U : CosimplicialObject C}
    (hU : IsPointResolution U) : IsIso (derivedColimitForgetComparison C B) := by
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory ⋙
          totalDerivedColimit C AddCommGrpCat.{u}) := by
    intro J
    have : PreservesColimitsOfShape (Discrete J) (forgetModuleDiagrams (C := C)
        (B := B)).mapDerivedCategory :=
      Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J
    infer_instance
  have : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      (totalDerivedColimit C (ModuleCat.{u} B) ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory) := by
    intro J
    have : PreservesColimitsOfShape (Discrete J)
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory :=
      Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory _ J
    infer_instance
  have hsep : (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} ↦ ModuleCat.of B B)).IsSeparating :=
    fun _ _ f g h ↦ StacksDraft.Perfect.isSeparator_regularModule f g fun G hG a ↦ by
      obtain rfl := (ObjectProperty.singleton_iff _ _).1 hG
      exact h _ ⟨PUnit.unit⟩ a
  exact StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel
    (fun _ : PUnit.{u + 1} ↦ ModuleCat.of B B)
    (fun _ ↦ StacksDraft.Perfect.isCompactObject_regularModule) hsep
    (derivedColimitForgetComparison C B) fun W _ ↦
      isIso_derivedColimitForgetComparison_app_single_freeYoneda C B hU W (ModuleCat.of B B)

/-- **The identification `Lπ_!(Ψ K) = Φ(Lπ_!(K))`**, as an isomorphism of functors
`D(Cᵒᵖ ⥤ Mod(B)) ⥤ D(Ab)` whose underlying morphism is
`Stacks.ChaoticSite.derivedColimitForgetComparison`. -/
def derivedColimitForgetComparisonNatIso {U : CosimplicialObject C} (hU : IsPointResolution U) :
    (forgetModuleDiagrams (C := C) (B := B)).mapDerivedCategory ⋙
        totalDerivedColimit C AddCommGrpCat.{u} ≅
      totalDerivedColimit C (ModuleCat.{u} B) ⋙
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapDerivedCategory :=
  haveI := isIso_derivedColimitForgetComparison C B hU
  asIso (derivedColimitForgetComparison C B)

end Stacks.ChaoticSite

end
