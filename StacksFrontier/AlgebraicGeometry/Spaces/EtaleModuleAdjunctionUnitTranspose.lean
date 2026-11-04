module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionConormalBaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# Transposes of the identification `φ^*𝒪 ≅ 𝒪` along the étale module adjunction

For a morphism `φ` of algebraic spaces the inverse image of modules has two adjunctions with a
direct image in the library: the étale module adjunction
(`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`) used by the base
change of the Zariski reading, and the adjunction of Stacks 03D7
(`AlgebraicGeometry.Space.modulePullbackAdjunction`).  Both are transports of one adjunction, and
their transposes agree on sections.  In particular the transpose of `φ^*𝒪 ≅ 𝒪` along the étale
module adjunction is the structure map of `φ` on sections.

## Main results

* `CategoryTheory.Adjunction.ofNatIsoRight_homEquiv_eq`: transposes along two transports of an
  adjunction differ by the transports.
* `AlgebraicGeometry.Space.etaleModuleAdjunction_homEquiv_val_app`: the two transposes agree on
  sections.
* `AlgebraicGeometry.Space.etaleModuleAdjunction_homEquiv_modulePullbackUnitIso_val_app`: the
  transpose of `φ^*𝒪 ≅ 𝒪` is the structure map, on sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.Adjunction

/-- Transposes along two transports of an adjunction along isomorphisms of right adjoints
differ by the two transports. -/
theorem ofNatIsoRight_homEquiv_eq {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R R₁ R₂ : D ⥤ C} (adj : L ⊣ R) (e₁ : R ≅ R₁) (e₂ : R ≅ R₂) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    (adj.ofNatIsoRight e₂).homEquiv X Y f =
      (adj.ofNatIsoRight e₁).homEquiv X Y f ≫ e₁.inv.app Y ≫ e₂.hom.app Y := by
  simp [Adjunction.homEquiv_unit]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Transposes along the étale module adjunction and along the module adjunction of Stacks 03D7
agree on sections. -/
theorem etaleModuleAdjunction_homEquiv_val_app {X Y : AlgebraicSpaces B S hS} (h : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {G : Modules.{u, u} B S hS X.1 X.2}
    (f : (modulePullback B S hS h).obj M ⟶ G) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : M.val.obj W) :
    (((smallEtaleRingedToposHom B S hS h).pullbackAdjPushforwardModulesViaComparison.homEquiv _ _
      f).val.app W s) =
      ((modulePullbackAdjunction B S hS h).homEquiv _ _ f).val.app W s := by
  rfl

/-- The transpose along the étale module adjunction of the identification `φ^*𝒪 ≅ 𝒪` is the
structure map, on sections. -/
theorem etaleModuleAdjunction_homEquiv_modulePullbackUnitIso_val_app
    {X Y : AlgebraicSpaces B S hS} (h : X ⟶ Y) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj W) :
    (((smallEtaleRingedToposHom B S hS h).pullbackAdjPushforwardModulesViaComparison.homEquiv _ _
      (modulePullbackUnitIso B S hS h).hom).val.app W s) =
      (pushforwardStructureProjection B S hS h).val.app W s :=
  (etaleModuleAdjunction_homEquiv_val_app h (modulePullbackUnitIso B S hS h).hom W s).trans
    (congrArg (fun k => k.val.app W s) (homEquiv_modulePullbackUnitIso_hom B S hS h))

end AlgebraicGeometry.Space

end
