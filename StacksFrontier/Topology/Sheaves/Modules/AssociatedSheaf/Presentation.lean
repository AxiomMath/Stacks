module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.Presentation.Finite
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Free

/-!
# Presentations of an associated sheaf of modules

Let `(X, 𝒪_X)` be a ringed space, `α : R → Γ(X, 𝒪_X)` a ring homomorphism and `M` an
`R`-module presented by generators and relations. Pushing the presentation of `M` through
construction (3) of Stacks 01BH gives a presentation of the associated sheaf by free sheaves of
`𝒪_X`-modules; when the presentation of `M` is finite, the associated sheaf is of finite
presentation.

## Main definitions

* `Stacks.AssociatedSheaf.presentationFreeRelationMap` and
  `Stacks.AssociatedSheaf.presentationFreeπ`: the relation map and the generator map of a module
  presentation, read on free sheaves of modules through `freeIsoAssociatedSheaf`.
* `Stacks.AssociatedSheaf.sheafPresentation`: the resulting
  `SheafOfModules.Presentation` of the associated sheaf.

## Main results

* `Stacks.AssociatedSheaf.isColimitPresentationFreeCofork`: the associated sheaf is the cokernel
  of `presentationFreeRelationMap`.
* `Stacks.AssociatedSheaf.associatedSheaf_isFinitePresentation`: the sheaf associated to a
  finitely presented module is of finite presentation.

## Implementation notes

Construction (3) is a left adjoint (`associatedSheafAdjunction`, Stacks 01BH(4)), so it preserves
the cokernel presenting `M` in `ModuleCat R`; the only further input is the identification of the
associated sheaf of a free module with a free sheaf of modules, which is
`freeIsoAssociatedSheaf`. Nothing here needs construction (2) of Stacks 01BH, and in particular
nothing needs its comparison with construction (3).

`Module.Presentation` is taken with both index types in the universe of the ringed space, which
is where `SheafOfModules.free` lives; `Module.finitePresentation_iff_exists_presentation` is
universe-polymorphic in them, so this costs nothing.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective
  isLeftAdjoint_associatedSheafFunctor

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

variable {M : ModuleCat.{u} R} (P : Module.Presentation.{u, u} R M)

/-- The relation map of a module presentation, as a morphism of free `R`-modules written at the
spelling `ModuleCat.free` uses, so that it composes with `freeIsoAssociatedSheaf`. -/
def presentationModuleMap : (ModuleCat.free R).obj P.R ⟶ (ModuleCat.free R).obj P.G :=
  ModuleCat.ofHom P.map

/-- The generator map of a module presentation, at the same spelling. -/
def presentationModuleπ : (ModuleCat.free R).obj P.G ⟶ M :=
  ModuleCat.ofHom P.toSolution.π

/-- The relation map of a module presentation followed by its generator map is zero. -/
lemma presentationModuleMap_comp_π :
    presentationModuleMap P ≫ presentationModuleπ P = 0 :=
  ModuleCat.hom_ext P.toSolution.π_comp_map

/-- The relation map of a module presentation, read as a morphism of free sheaves of
`𝒪_X`-modules through `freeIsoAssociatedSheaf`. -/
def presentationFreeRelationMap :
    SheafOfModules.free (R := structureSheafRing X) P.R ⟶
      SheafOfModules.free P.G :=
  (freeIsoAssociatedSheaf X α P.R).hom ≫
    (associatedSheafFunctor.{u, u} X α).map (presentationModuleMap P) ≫
    (freeIsoAssociatedSheaf X α P.G).inv

/-- The generator map of a module presentation, read as a morphism from a free sheaf of
`𝒪_X`-modules to the associated sheaf. -/
def presentationFreeπ :
    SheafOfModules.free (R := structureSheafRing X) P.G ⟶
      (associatedSheafFunctor.{u, u} X α).obj M :=
  (freeIsoAssociatedSheaf X α P.G).hom ≫
    (associatedSheafFunctor.{u, u} X α).map (presentationModuleπ P)

/-- The relation map on free sheaves of modules followed by the generator map to the associated
sheaf is zero. -/
lemma presentationFreeRelationMap_comp_π :
    presentationFreeRelationMap X α P ≫ presentationFreeπ X α P = 0 := by
  rw [presentationFreeRelationMap, presentationFreeπ, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← Functor.map_comp, presentationModuleMap_comp_π, Functor.map_zero,
    comp_zero]

/-- Construction (3) of Stacks 01BH preserves the cokernel presenting `M`: the associated sheaf
is the cokernel of the relation map on free sheaves of modules. -/
def isColimitPresentationFreeCofork :
    IsColimit (CokernelCofork.ofπ (presentationFreeπ X α P)
      (presentationFreeRelationMap_comp_π X α P)) := by
  refine IsCokernel.ofIso _
    (CokernelCofork.mapIsColimit _
      (ModuleCat.isColimitCokernelCofork (presentationModuleMap P)
        (presentationModuleπ P) P.toIsPresentation.exact
        P.toIsPresentation.surjective_π)
      (associatedSheafFunctor.{u, u} X α))
    _ (freeIsoAssociatedSheaf X α P.R).symm (freeIsoAssociatedSheaf X α P.G).symm
    (Iso.refl _) ?_ ?_
  · simp only [Iso.symm_hom, presentationFreeRelationMap, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Cofork.π_ofπ, presentationFreeπ, Iso.inv_hom_id_assoc, Iso.refl_hom,
      Category.comp_id, CokernelCofork.map_π]

/-- The presentation of the associated sheaf obtained from a presentation of the module. -/
def sheafPresentation : ((associatedSheafFunctor.{u, u} X α).obj M).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree (presentationFreeRelationMap X α P)
    (presentationFreeπ X α P) (presentationFreeRelationMap_comp_π X α P)
    (isColimitPresentationFreeCofork X α P)

/-- The presentation of the associated sheaf obtained from a finite module presentation is
finite. -/
instance sheafPresentation_isFinite [Finite P.G] [Finite P.R] :
    (sheafPresentation X α P).IsFinite :=
  ⟨⟨inferInstanceAs (Finite P.G)⟩, ⟨inferInstanceAs (Finite P.R)⟩⟩

/-- **Stacks 01BH and 01BD.** The sheaf of `𝒪_X`-modules associated to a finitely presented
`R`-module is of finite presentation. -/
theorem associatedSheaf_isFinitePresentation (N : ModuleCat.{u} R)
    [Module.FinitePresentation R N] : (associatedSheaf X α N).IsFinitePresentation := by
  classical
  obtain ⟨Q, _, _⟩ :=
    (Module.finitePresentation_iff_exists_presentation.{u, u} (A := R) (M := N)).mp inferInstance
  refine SheafOfModules.IsFinitePresentation.mk.{u, u, u}
    ⟨(sheafPresentation X α Q).quasicoherentData, ?_⟩
  constructor
  intro _
  exact ⟨⟨inferInstanceAs (Finite Q.G)⟩, ⟨inferInstanceAs (Finite Q.R)⟩⟩

end Stacks.AssociatedSheaf
