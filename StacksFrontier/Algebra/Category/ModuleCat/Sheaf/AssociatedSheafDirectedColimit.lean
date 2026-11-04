module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.FinitePresentation.Colimit
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Presentation

/-!
# Associated sheaves as directed colimits of finitely presented sheaves

The sheaf of `𝒪_X`-modules associated to a module over a ring mapping to the global sections of a
ringed space is a directed colimit of sheaves of modules of finite presentation.

## Main results

* `Stacks.AssociatedSheaf.exists_directed_system_of_isFinitePresentation`: **Tag 01BR**, a
  directed system of finitely presented sheaves of modules whose colimit is the associated sheaf.

## Implementation notes

Every module is a directed colimit of finitely presented modules
(`Module.exists_linearEquiv_directLimit_finitePresentation_max`, Stacks 00HA), construction (3)
of Stacks 01BH is a left adjoint and so preserves that colimit, and the associated sheaf of a
finitely presented module is of finite presentation
(`Stacks.AssociatedSheaf.associatedSheaf_isFinitePresentation`). No part of this needs
construction (2) of Stacks 01BH.

A homomorphism from an arbitrary commutative ring to the global sections is allowed; taking it to
be the identity gives the source statement. A directed system is a functor from a nonempty
directed preorder, and its maps to the associated sheaf are given as a colimit cocone, so the
identification is with that particular sheaf rather than with an abstract isomorphic one.

## References

* [Stacks Project, Tag 01BR](https://stacks.math.columbia.edu/tag/01BR)
* [Stacks Project, Tag 00HA](https://stacks.math.columbia.edu/tag/00HA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

/-- **Stacks 01BR.** The sheaf associated to a module over a ring mapping to the global sections
of a ringed space is a directed colimit of sheaves of modules of finite presentation. -/
@[stacks 01BR]
theorem exists_directed_system_of_isFinitePresentation (X : RingedSpace.{u, u}) {R : Type u}
    [CommRing R] (α : R →+* X.presheaf.obj (op ⊤)) (M : ModuleCat.{u} R) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ SheafOfModules.{u} (structureSheafRing X))
      (φ : D ⟶ (Functor.const I).obj (associatedSheaf X α M)),
      (∀ i, (D.obj i).IsFinitePresentation) ∧
        Nonempty (IsColimit (Cocone.mk (associatedSheaf X α M) φ)) := by
  classical
  obtain ⟨I, hpre, hdir, hne, hdec, G, hGadd, hGmod, f, hf, hfp, ⟨e⟩⟩ :=
    Module.exists_linearEquiv_directLimit_finitePresentation_max.{u, u} R M
  let D₀ : I ⥤ ModuleCat.{u} R := ModuleCat.directLimitDiagram G f
  let c₀ : Cocone D₀ := ModuleCat.directLimitCocone G f
  let F := associatedSheafFunctor.{u, u} X α
  have := (associatedSheafAdjunction.{u, u} X α).isLeftAdjoint
  let eIso : associatedSheaf X α M ≅ (F.mapCocone c₀).pt := F.mapIso e.toModuleIso
  let t : Cocone (D₀ ⋙ F) := (F.mapCocone c₀).extend eIso.inv
  have ht : IsColimit t :=
    IsColimit.ofIsoColimit (isColimitOfPreserves F (ModuleCat.directLimitIsColimit G f))
      (Cocone.ext eIso.symm fun _ ↦ rfl)
  refine ⟨I, hpre, hne, hdir, D₀ ⋙ F, t.ι, fun i ↦ ?_, ⟨ht⟩⟩
  have : Module.FinitePresentation R (G i) := hfp i
  exact associatedSheaf_isFinitePresentation X α (ModuleCat.of R (G i))

end Stacks.AssociatedSheaf
