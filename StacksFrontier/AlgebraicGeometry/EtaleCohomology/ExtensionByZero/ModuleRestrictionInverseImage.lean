module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction and inverse image of sheaves of modules along an étale morphism

For an étale morphism `j : U ⟶ X` and a ring `Λ` there are two readings of `j^{-1}` on sheaves
of `Λ`-modules on the small étale site: the sheafified inverse image along base change, and
restriction along composition with `j`. This file shows they agree, by exhibiting both as left
adjoints of the direct image formed from base change.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u r

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- Restriction of sheaves of `Λ`-modules along an étale morphism is left adjoint to the direct
image formed from base change: both functors are precomposition along a functor of small étale
sites, and composition with `j` is left adjoint to base change along `j`. -/
def etaleModuleRestrictionDirectImageAdj :
    etaleModuleRestriction.{u, r} Λ j ⊣ etaleModuleDirectImage.{u, r} Λ j :=
  ((smallEtaleComposeBaseChangeAdj j).op.whiskerLeft
      (ModuleCat.{max (u + 1) r} Λ)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- For an étale morphism the two readings of `j^{-1}` on sheaves of `Λ`-modules agree: the
inverse image along base change is isomorphic to restriction, both being left adjoints of the
direct image along base change. -/
def etaleModuleInverseImageRestrictionIso :
    etaleModuleInverseImage.{u, r} Λ j ≅ etaleModuleRestriction.{u, r} Λ j :=
  Adjunction.leftAdjointUniq (etaleModuleInverseImageAdj.{u, r} Λ j)
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ j)

/-- The direct image `j_*` of sheaves of `Λ`-modules along an étale morphism `j : U ⟶ X` of the
small étale sites: the right Kan extension along composition with `j`. -/
abbrev etaleModuleEtaleDirectImage :
    EtaleModules.{u, r} Λ U ⥤ EtaleModules.{u, r} Λ X :=
  (smallEtaleCompose j).sheafPushforwardCocontinuous
    (ModuleCat.{max (u + 1) r} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction of sheaves of modules along an étale morphism is left adjoint to the direct
image `j_*`. -/
def etaleModuleEtaleDirectImageAdj :
    etaleModuleRestriction.{u, r} Λ j ⊣ etaleModuleEtaleDirectImage.{u, r} Λ j :=
  Functor.sheafAdjunctionCocontinuous _ _ _ _

/-- For an étale monomorphism the counit `j^{-1} j_* F ⟶ F` of sheaves of modules is an
isomorphism: it is the counit of the right Kan extension along a fully faithful functor of
sites, and `sheafToPresheaf` reflects isomorphisms. -/
instance etaleModuleEtaleDirectImageAdj_counit_app_isIso [Mono j] (F : EtaleModules.{u, r} Λ U) :
    IsIso ((etaleModuleEtaleDirectImageAdj.{u, r} Λ j).counit.app F) := by
  have hcounit : ((etaleModuleEtaleDirectImageAdj.{u, r} Λ j).counit.app F).hom =
      ((smallEtaleCompose j).op.ranAdjunction (ModuleCat.{max (u + 1) r} Λ)).counit.app F.obj :=
    Functor.sheafAdjunctionCocontinuous_counit_app_hom _ _ _ _ F
  have happ : ∀ V, IsIso (((smallEtaleCompose j).op.ranCounit.app F.obj).app V) := fun V =>
    (Functor.isPointwiseRightKanExtensionRanCounit (smallEtaleCompose j).op F.obj
      ((smallEtaleCompose j).op.obj V)).isIso_hom_app
  have : IsIso ((sheafToPresheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map
      ((etaleModuleEtaleDirectImageAdj.{u, r} Λ j).counit.app F)) := by
    change IsIso ((etaleModuleEtaleDirectImageAdj.{u, r} Λ j).counit.app F).hom
    rw [hcounit, Functor.ranAdjunction_counit]
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  exact isIso_of_reflects_iso _ (sheafToPresheaf U.smallEtaleTopology _)

/-- For an étale monomorphism the counit of `j^{-1} ⊣ j_*` is an isomorphism of functors. -/
instance etaleModuleEtaleDirectImageAdj_counit_isIso [Mono j] :
    IsIso (etaleModuleEtaleDirectImageAdj.{u, r} Λ j).counit :=
  NatIso.isIso_of_isIso_app _

/-- The unit of `j_! ⊣ j^{-1}` is an isomorphism for an étale monomorphism: in the adjoint
triple `j_! ⊣ j^{-1} ⊣ j_*` the unit of the first adjunction is invertible exactly when the
counit of the second is. -/
instance isIso_etaleModuleExtensionByZeroAdj_unit [Mono j] :
    IsIso (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨etaleModuleExtensionByZeroAdj.{u, r} Λ j,
      etaleModuleEtaleDirectImageAdj.{u, r} Λ j⟩).2 inferInstance

/-- For an étale monomorphism `j`, the counit `j_! j^{-1} F ⟶ F` of sheaves of modules becomes
invertible after restriction along `j`. -/
theorem isIso_etaleModuleRestriction_map_counit [Mono j] (F : EtaleModules.{u, r} Λ X) :
    IsIso ((etaleModuleRestriction.{u, r} Λ j).map
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit.app F)) := by
  let ff := (etaleModuleExtensionByZeroAdj.{u, r} Λ j).fullyFaithfulLOfIsIsoUnit
  let _ := ff.full
  let _ := ff.faithful
  infer_instance

/-- The endofunctor `j_! j^{-1}` of sheaves of `Λ`-modules on the small étale site of `X`, for
an étale morphism `j : U ⟶ X`. -/
abbrev etaleModuleExtensionByZeroOfRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    EtaleModules.{u, r} Λ X ⥤ EtaleModules.{u, r} Λ X :=
  etaleModuleRestriction.{u, r} Λ j ⋙ etaleModuleExtensionByZero.{u, r} Λ j

/-- The stalk at a geometric point `s` of `Y` of the inverse image along `f : Y ⟶ X` of a sheaf
of `Λ`-modules on the small étale site of `X` is the stalk of that sheaf at the image geometric
point `s ≫ f`, naturally in the sheaf. -/
def etaleModuleInverseImageSheafFiberIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    etaleModuleInverseImage.{u, r} Λ f ⋙
        ((pointSmallEtale s).ulift.{max (u + 1) r}).sheafFiber ≅
      ((pointSmallEtale (s ≫ f)).ulift.{max (u + 1) r}).sheafFiber :=
  let G := smallEtaleBaseChange f
  let Φ := (pointSmallEtale s).ulift.{max (u + 1) r}
  have hG : CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology G :=
    CoverPreserving.of_isContinuous _ _ _
  let _ : InitiallySmall.{max (u + 1) r} (G ⋙ Φ.fiber).Elements :=
    initiallySmall_of_essentiallySmall _
  let e : ((pointSmallEtale (s ≫ f)).ulift.{max (u + 1) r}).fiber ≅ (Φ.comap G hG).fiber :=
    Functor.isoWhiskerRight (pointSmallEtaleBaseChangeFiberIso f s)
        uliftFunctor.{max (u + 1) r, u} ≪≫
      Functor.associator _ _ _
  (Φ.sheafFiberComapIso G hG (ModuleCat.{max (u + 1) r} Λ)).symm ≪≫
    (GrothendieckTopology.Point.sheafFiberIso
      (GrothendieckTopology.Point.isoOfFiberIso e) (ModuleCat.{max (u + 1) r} Λ)).symm

end Stacks.EtaleCohomology

end
