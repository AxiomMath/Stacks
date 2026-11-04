module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafTerminology
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Pullback of a sheaf associated to a module

Let `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces. Pulling back the sheaf of
`𝒪_X`-modules associated to a `Γ(X, 𝒪_X)`-module `M` gives the sheaf of `𝒪_Y`-modules
associated to the extension of scalars of `M` along the induced map `Γ(X, 𝒪_X) → Γ(Y, 𝒪_Y)`
on global sections, naturally in `M`.

## Main definitions

* `Stacks.AssociatedSheaf.ringedSpacePullbackAssociatedSheafIso`: the comparison isomorphism
  `g^* ∘ (-)^~ ≅ (-)^~ ∘ (𝒪_Y(Y) ⊗_{𝒪_X(X)} -)`.

## Implementation notes

The isomorphism is obtained from uniqueness of left adjoints rather than by comparing the two
sheafifications directly. Both sides are left adjoints: the left-hand side is the composite of
the tensor-sheafification adjunction of Stacks 01BH(4) with the pullback-pushforward adjunction
of Stacks 0096, and the right-hand side is the composite of extension of scalars with the
tensor-sheafification adjunction on `Y`. Their right adjoints agree, by `rhsIso`: pushing a
sheaf of `𝒪_Y`-modules forward to `X` and taking global sections over `X` is the same as taking
global sections over `Y` and restricting scalars. That identification is componentwise the
reassociation of two restrictions of scalars along ring maps that are the identity, which is
what `ModuleCat.restrictScalarsId'App` provides.

The construction is read at `RingedSpace.{u, u}` and at the module universe equal to the space
universe. This is forced by main's vocabulary and not a choice: `associatedSheafFunctor.{u, v}`
lands in `SheafOfModules.{max u v}`, while `RingedSpaceModuleAdjunction.modulePullback` exists
only for `SheafOfModules.{u}` because Mathlib's
`PresheafOfModules.instIsRightAdjointPushforward` ties the site and module universes together
(see the implementation notes of
`StacksFrontier/Topology/Sheaves/Functors/Module/RingedSpace.lean`). So the composite in the
statement forces `max u v = u`.

## References

* [Stacks Project, Tag 01BJ](https://stacks.math.columbia.edu/tag/01BJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

/-- Pushing a sheaf of `𝒪_Y`-modules forward along `g` and taking global sections over `X` is
taking global sections over `Y` and restricting scalars along the map on global sections. -/
def modulePushforwardGlobalSectionsIso {X Y : RingedSpace.{u, u}} (g : Y ⟶ X) :
    RingedSpaceModuleAdjunction.modulePushforward g ⋙
        globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤))) ≅
      globalSectionsFunctor.{u, u} Y (RingHom.id (Y.presheaf.obj (op ⊤))) ⋙
        ModuleCat.restrictScalars (SheafedSpace.Γ.map g.op).hom := by
  let αX := RingHom.id (X.presheaf.obj (op ⊤))
  let αY := RingHom.id (Y.presheaf.obj (op ⊤))
  let f := (SheafedSpace.Γ.map g.op).hom
  have hf : f = (g.hom.c.app (op ⊤)).hom := by
    ext r
    simp [f]
  let rhsIso : RingedSpaceModuleAdjunction.modulePushforward g ⋙
      globalSectionsFunctor.{u, u} X αX ≅
      globalSectionsFunctor.{u, u} Y αY ⋙ ModuleCat.restrictScalars f :=
    NatIso.ofComponents (fun F => by
      let S := (globalSectionsFunctor.{u, u} X αX).obj
        ((RingedSpaceModuleAdjunction.modulePushforward g).obj F)
      let M := F.val.obj (op ⊤)
      let idX := RingHom.id ((structureSheafRing X).obj.obj (op ⊤))
      let idY := RingHom.id ((structureSheafRing Y).obj.obj (op ⊤))
      let Mx := (ModuleCat.restrictScalars (g.hom.c.app (op ⊤)).hom).obj M
      let qX : (X.presheaf.obj (op ⊤)) →+* X.presheaf.obj (op ⊤) := RingCat.Hom.hom
        ((Functor.whiskerRight (globalSectionsMap X αX) (forget₂ CommRingCat RingCat)).app (op ⊤))
      let qY : (Y.presheaf.obj (op ⊤)) →+* Y.presheaf.obj (op ⊤) := RingCat.Hom.hom
        ((Functor.whiskerRight (globalSectionsMap Y αY) (forget₂ CommRingCat RingCat)).app (op ⊤))
      have hqX : qX = RingHom.id (X.presheaf.obj (op ⊤)) := by
        ext r
        simp [qX, globalSectionsMap]
        rfl
      have hqY : qY = RingHom.id (Y.presheaf.obj (op ⊤)) := by
        ext r
        simp [qY, globalSectionsMap]
        rfl
      have eS : S ≅ Mx := by
        dsimp only [S, M, Mx, idX, αX, globalSectionsFunctor,
          RingedSpaceModuleAdjunction.modulePushforward,
          RingedSpaceModuleAdjunction.structureSheafHom,
          Stacks.PresheafOfModules.ChangeOfRings.restrictScalars, PresheafOfModules.restrictScalars,
          PresheafOfModules.restrictScalarsObj, PresheafOfModules.evaluation,
          SheafOfModules.pushforward, Functor.comp]
        exact (ModuleCat.restrictScalarsId'App qX hqX ((ModuleCat.restrictScalars idX).obj Mx)) ≪≫
          ModuleCat.restrictScalarsId'App idX rfl Mx
      have eY : (globalSectionsFunctor.{u, u} Y αY).obj F ≅ M := by
        dsimp only [M, idY, αY, globalSectionsFunctor,
          Stacks.PresheafOfModules.ChangeOfRings.restrictScalars, PresheafOfModules.restrictScalars,
          PresheafOfModules.restrictScalarsObj, PresheafOfModules.evaluation,
          Functor.comp]
        exact (ModuleCat.restrictScalarsId'App qY hqY ((ModuleCat.restrictScalars idY).obj M)) ≪≫
          ModuleCat.restrictScalarsId'App idY rfl M
      exact eS ≪≫ (ModuleCat.restrictScalarsCongr hf).symm.app M ≪≫
        ((ModuleCat.restrictScalars f).mapIso eY).symm) (by
      intro F G h
      ext x
      simp [Stacks.PresheafOfModules.ChangeOfRings.restrictScalars,
        PresheafOfModules.restrictScalars,
        PresheafOfModules.evaluation, SheafOfModules.pushforward,
        RingedSpaceModuleAdjunction.modulePushforward]
      rfl)
  exact rhsIso

/-- **Stacks 01BJ.** The pullback of the sheaf associated to a module is the sheaf associated to
the module obtained by extension of scalars along the map on global sections.

The name says `ringedSpace` because `Stacks.AssociatedSheaf.pullbackAssociatedSheafIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos` is a different
comparison, between the coefficient-point pullback and the associated-sheaf functor. -/
@[stacks 01BJ]
def ringedSpacePullbackAssociatedSheafIso {X Y : RingedSpace.{u, u}} (g : Y ⟶ X) :
    associatedSheafFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤))) ⋙
        RingedSpaceModuleAdjunction.modulePullback g ≅
      ModuleCat.extendScalars (SheafedSpace.Γ.map g.op).hom ⋙
        associatedSheafFunctor.{u, u} Y (RingHom.id (Y.presheaf.obj (op ⊤))) := by
  let adj₁ := (associatedSheafAdjunction.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤)))).comp
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction g)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj (SheafedSpace.Γ.map g.op).hom).comp
    (associatedSheafAdjunction.{u, u} Y (RingHom.id (Y.presheaf.obj (op ⊤))))
  exact Adjunction.leftAdjointUniq adj₁
    (adj₂.ofNatIsoRight (modulePushforwardGlobalSectionsIso g).symm)

end Stacks.AssociatedSheaf
