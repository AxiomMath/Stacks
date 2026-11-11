module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesULiftComparison

/-!
# Higher cohomology of the structure sheaf over an affine object, at module universe `u + 1`

Let `𝒳` be an algebraic stack over `S`, whose site has objects in `Type (u + 1)` and morphisms in
`Type u`, and let `x` be an object of `𝒳` lying over an affine scheme. This file proves

`Hⁱ(x, 𝒪_𝒳) = 0` for `i > 0`,

where the cohomology is the right derived functor of the sections over `x` on the fppf modules
at module universe `u + 1`, and `𝒪_𝒳` is the structure sheaf with its sections raised to `u + 1`.

At module universe `u` this is
`AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine` (Stacks 03F9 with
Stacks 03FJ), once the structure sheaf is known to be cartesian along flat
morphisms of affines: the comparison `Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} Γ(X, 𝒪) ⟶ Γ(Z, 𝒪)` is the
isomorphism `B ⊗_A A ≅ B`. The universe lift of modules is exact and preserves injective objects
(`AlgebraicGeometry.Stack.preservesInjectiveObjects_fppfModulesULift`) and commutes with
sections over `x`, so the right derived functors of sections over `x` at `u + 1`, evaluated at
the lift of a module, are the lifts of those at `u`.

## Main results

* `AlgebraicGeometry.FibredSite.isCartesianAlongFlatAffines_unit`: the structure sheaf is
  cartesian along flat morphisms of affines.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_unit_of_isAffineOver`: the vanishing
  at module universe `u`.
* `AlgebraicGeometry.Stack.rightDerivedEvaluationModuleULiftIso`: the right derived functors of
  sections over an object commute with the universe lift.
* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver`: **the
  vanishing at module universe `u + 1`**.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The free presheaf of modules of rank one over the structure presheaf is the structure presheaf
with its sections lifted to the same universe. -/
def largeUnitIsoUnit :
    Stacks.PresheafOfModules.largeUnit.{v, u, u, u} (Stack.structureSheaf B S hS p hp
        (etaleTopology B) (Stack.etaleTopology_le_topology B)).obj ≅
      PresheafOfModules.unit ((Stack.structureSheaf B S hS p hp (etaleTopology B)
        (Stack.etaleTopology_le_topology B)).obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.isoMk (fun X =>
    { hom := ModuleCat.ofHom
        (X := (Stacks.PresheafOfModules.largeUnit.{v, u, u, u} (Stack.structureSheaf B S hS p hp
          (etaleTopology B) (Stack.etaleTopology_le_topology B)).obj).obj X)
        (Y := (PresheafOfModules.unit ((Stack.structureSheaf B S hS p hp (etaleTopology B)
          (Stack.etaleTopology_le_topology B)).obj ⋙ forget₂ CommRingCat RingCat)).obj X)
        { toFun := fun a => a.down
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      inv := ModuleCat.ofHom
        (X := (PresheafOfModules.unit ((Stack.structureSheaf B S hS p hp (etaleTopology B)
          (Stack.etaleTopology_le_topology B)).obj ⋙ forget₂ CommRingCat RingCat)).obj X)
        (Y := (Stacks.PresheafOfModules.largeUnit.{v, u, u, u} (Stack.structureSheaf B S hS p hp
          (etaleTopology B) (Stack.etaleTopology_le_topology B)).obj).obj X)
        { toFun := fun a => ULift.up a
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      hom_inv_id := rfl
      inv_hom_id := rfl })
    (fun _ _ _ => rfl)

/-- **The structure sheaf is cartesian along flat morphisms of affines**: the comparison
`Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} Γ(X, 𝒪) ⟶ Γ(Z, 𝒪)` is an isomorphism. -/
theorem isCartesianAlongFlatAffines_unit :
    IsCartesianAlongFlatAffines B S hS p hp
      (SheafOfModules.unit (ringStructureSheafCore B S hS p hp .fppf)) :=
  Stack.isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange B S hS p hp _
    (fun φ _ _ _ =>
      have := Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit.{v, u, u, u}
        (Stack.structureSheaf B S hS p hp (etaleTopology B)
          (Stack.etaleTopology_le_topology B)).obj φ.op
      Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso
        (largeUnitIsoUnit B S hS p hp) φ.op)

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

section ModuleUniverse

attribute [local instance] enoughInjectives_fppfModules

/-- **The higher cohomology of the structure sheaf over an object lying over an affine scheme
vanishes**, at module universe `u`. -/
theorem isZero_rightDerived_evaluation_unit_of_isAffineOver {x : 𝒳.val.val.obj}
    (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) (i : ℕ) (hi : 0 < i) :
    IsZero (((SheafOfModules.evaluation.{u} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) (op x)).rightDerived i).obj
        (SheafOfModules.unit _)) := by
  let : IsGrothendieckAbelian.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  have : LocallySmall.{u + 1}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    locallySmall_self _
  have : LocallySmall.{u + 1} (fppfModules B S hS 𝒳) := locallySmall_self _
  let : HasExt.{u + 1}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{u + 1} (fppfModules B S hS 𝒳) := hasExt_of_enoughInjectives _
  exact FibredSite.isZero_rightDerived_evaluation_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids _
    (FibredSite.isCartesianAlongFlatAffines_unit B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)
    hx i hi

end ModuleUniverse

section ModuleUniverseSucc

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ enoughInjectives_fppfModulesUnivLESucc
  enoughInjectives_fppfModules

/-- Sections over an object commute with the universe lift of modules from `u` to `u + 1`. -/
def evaluationModuleULiftIso (x : 𝒳.val.val.obj) :
    SheafOfModules.evaluation.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf) (op x) ⋙ ModuleCat.uliftFunctor.{u + 1} _ ≅
      Stacks.SheafOfModules.moduleULift.{u + 1, u} (FibredSite.ringStructureSheafCore B S hS
          𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) ⋙
        SheafOfModules.evaluation.{u + 1} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) (op x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The right derived functors of sections over an object commute with the universe lift** of
modules on an algebraic stack from `u` to `u + 1`: the lift is exact and preserves injective
objects, and commutes with sections over `x`. -/
def rightDerivedEvaluationModuleULiftIso (x : 𝒳.val.val.obj) (i : ℕ)
    (F : fppfModules B S hS 𝒳) :
    (ModuleCat.uliftFunctor.{u + 1} _).obj
        (((SheafOfModules.evaluation.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) (op x)).rightDerived i).obj F) ≅
      ((SheafOfModules.evaluation.{u + 1} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids .fppf) (op x)).rightDerived i).obj
        ((Stacks.SheafOfModules.moduleULift.{u + 1, u} (FibredSite.ringStructureSheafCore B S hS
          𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).obj F) :=
  haveI : (Stacks.SheafOfModules.moduleULift.{u + 1, u} (FibredSite.ringStructureSheafCore
      B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).PreservesInjectiveObjects :=
    preservesInjectiveObjects_fppfModulesULift B S hS 𝒳
  haveI : (Stacks.SheafOfModules.moduleULift.{u + 1, u} (FibredSite.ringStructureSheafCore
      B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)).PreservesHomology :=
    preservesHomology_fppfModulesULift 𝒳
  haveI : (ModuleCat.uliftFunctor.{u + 1} ((FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj.obj (op x))).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  ((Functor.rightDerivedCompIso _ (ModuleCat.uliftFunctor.{u + 1} _) i).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (evaluationModuleULiftIso B S hS 𝒳 x) i).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects
      (Stacks.SheafOfModules.moduleULift.{u + 1, u} _) _ F i

/-- **The higher cohomology of the structure sheaf over an object lying over an affine scheme
vanishes at module universe `u + 1`**: for every algebraic stack `𝒳`, every object `x` of `𝒳`
lying over an affine scheme and every `i > 0`, `Hⁱ(x, 𝒪_𝒳) = 0`, where `𝒪_𝒳` is the structure
sheaf with its sections raised to `u + 1` and the cohomology is computed among the fppf modules
at module universe `u + 1`. -/
theorem isZero_rightDerived_evaluation_uliftUnit_of_isAffineOver {x : 𝒳.val.val.obj}
    (hx : IsAffineOver B S hS (𝒳.val.val.p.obj x)) (i : ℕ) (hi : 0 < i) :
    IsZero (((SheafOfModules.evaluation.{u + 1} (FibredSite.ringStructureSheafCore B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) (op x)).rightDerived i).obj
        (Stacks.SheafOfModules.uliftUnit.{u + 1} _)) :=
  IsZero.of_iso (Functor.map_isZero _
      (isZero_rightDerived_evaluation_unit_of_isAffineOver B S hS 𝒳 hx i hi))
    (rightDerivedEvaluationModuleULiftIso B S hS 𝒳 x i _).symm

end ModuleUniverseSucc

end AlgebraicGeometry.Stack
