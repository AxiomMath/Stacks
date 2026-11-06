module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModules
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ModuleScalarAction

/-!
# Finite modules with a continuous action as discrete modules with scalar operations

Let `Λ` be a **finite** ring and `G` a topological group. A finite `Λ`-module with a continuous
`G`-action is the same thing as a finite discrete `G`-module together with additive scalar
operations, that is, an additive functor from `CategoryTheory.SingleObj Λ` to the finite
discrete `G`-modules.

This is the right-hand-side half of the device by which part (2) of Stacks Tag 0DV5 is upgraded
to part (3): the left-hand-side half is
`CategoryTheory.moduleSheafScalarActionEquivalence`.

## Main results

* `Stacks.GroupCohomology.moduleCat_isFG_iff_finite` — over a finite ring, finite generation of
  a module is finiteness of its carrier.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleScalarActionEquivalence` — the equivalence.

## Implementation notes

The scalar operations of a `Λ`-`G`-module commute with the action by definition: the action is
by morphisms of `ModuleCat Λ`, that is, by `Λ`-linear maps. That is exactly what makes
multiplication by `a : Λ` a morphism of discrete `G`-modules, and it is where the "commuting"
of the source's "finite `π₁(X, x̄)`-modules endowed with commuting `Λ`-module structure" is
located.

Both functors of the equivalence are the identity on underlying abelian groups, so the unit and
counit are identities and the equivalence is strict on underlying data.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5), part (3)
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Stacks.GroupCohomology

/-- Over a finite ring a module is finitely generated exactly when its carrier is finite. -/
public theorem moduleCat_isFG_iff_finite (Λ : Type u) [Ring Λ] [Finite Λ]
    (M : ModuleCat.{w} Λ) : ModuleCat.isFG Λ M ↔ Finite (ToType M) := by
  rw [ModuleCat.isFG_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Module.Finite Λ M := h
    exact Module.finite_of_finite Λ
  · have : Finite (ToType M) := h
    infer_instance

section Scalars

variable (Λ : Type u) [Ring Λ] (G : Type v) [Group G] [TopologicalSpace G]

/-- Continuous actions of `G` on abelian groups form a preadditive category: the hom sets are
those of `Action AddCommGrpCat G`. -/
public instance preadditive_contAction_addCommGrp :
    Preadditive (ContAction AddCommGrpCat.{w} G) :=
  Preadditive.fullSubcategory _

/-- Discrete `G`-modules form a preadditive category. -/
public instance preadditive_continuousGAddCommGrp :
    Preadditive (ContinuousGAddCommGrp.{v, w} G) :=
  Preadditive.fullSubcategory _

/-- Finite discrete `G`-modules form a preadditive category. -/
public instance preadditive_finiteContinuousGAddCommGrp :
    Preadditive (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory :=
  Preadditive.fullSubcategory _

/-- Two morphisms of finite discrete `G`-modules agree as soon as their underlying maps do. -/
public theorem finiteContinuousAbelianHom_ext
    {M N : (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory} {f g : M ⟶ N}
    (h : f.hom.hom.hom.hom.hom = g.hom.hom.hom.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
    Action.Hom.ext <| AddCommGrpCat.hom_ext h

/-- The finite discrete `G`-module underlying a finite `Λ`-`G`-module. -/
public def finiteTypeContinuousModuleForgetAbelian [Finite Λ] :
    FiniteTypeContinuousModule.{u, v, w} Λ G ⥤
      (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory where
  obj M := by
    let A : Action AddCommGrpCat.{w} G :=
      { V := AddCommGrpCat.of (ToType M.obj.obj.obj.V)
        ρ :=
          { toFun := fun g ↦ End.of
              (AddCommGrpCat.ofHom (M.obj.obj.obj.ρ g).asHom.hom.toAddMonoidHom)
            map_one' := by
              apply End.ext
              apply AddCommGrpCat.hom_ext
              ext x
              simp
            map_mul' := by
              intro _ _
              apply End.ext
              apply AddCommGrpCat.hom_ext
              ext x
              simp [End.mul_asHom] } }
    let A' : ContAction AddCommGrpCat.{w} G := ⟨A, by
      refine (Action.isContinuous_def _).2 ?_
      exact (Action.isContinuous_def M.obj.obj.obj).mp M.obj.obj.property⟩
    refine ⟨⟨A', by
      change DiscreteTopology (TopCat.discrete.obj (AddCommGrpCat.of (ToType M.obj.obj.obj.V)))
      infer_instance⟩, ?_⟩
    exact (moduleCat_isFG_iff_finite Λ _).mp M.property
  map f := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom f.hom.hom.hom.hom.hom.toAddMonoidHom
      comm := fun g ↦ by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.hom.hom.comm g) x }))
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Scalar multiplication on a finite `Λ`-`G`-module, as a functor from the one-object category
on `Λ`: multiplication by `a` is a morphism of discrete `G`-modules because the action is by
`Λ`-linear maps. -/
public def finiteContinuousScalarFunctor [Finite Λ]
    (M : FiniteTypeContinuousModule.{u, v, w} Λ G) :
    SingleObj Λ ⥤ (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory where
  obj _ := (finiteTypeContinuousModuleForgetAbelian Λ G).obj M
  map a := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun := fun x ↦ a • x
          map_zero' := smul_zero a
          map_add' := smul_add a }
      comm := fun g ↦ by
        ext x
        exact ((M.obj.obj.obj.ρ g).asHom.hom.map_smul a x).symm }))
  map_id _ := by
    apply finiteContinuousAbelianHom_ext
    ext x
    exact one_smul Λ (show ToType M.obj.obj.obj.V from x)
  map_comp a b := by
    apply finiteContinuousAbelianHom_ext
    ext x
    exact mul_smul (show Λ from b) (show Λ from a) (show ToType M.obj.obj.obj.V from x)

/-- The scalar operations on a finite `Λ`-`G`-module are additive in the scalar, since
`(a + b) • x = a • x + b • x`. -/
public instance finiteContinuousScalarFunctor_additive [Finite Λ]
    (M : FiniteTypeContinuousModule.{u, v, w} Λ G) :
    (finiteContinuousScalarFunctor Λ G M).Additive where
  map_add := by
    rintro ⟨⟩ ⟨⟩ a b
    apply finiteContinuousAbelianHom_ext
    ext x
    exact add_smul (show Λ from a) (show Λ from b) (show ToType M.obj.obj.obj.V from x)

/-- A finite `Λ`-`G`-module, read as a finite discrete `G`-module with additive scalar
operations. -/
public def finiteTypeContinuousModuleToScalarAction [Finite Λ] :
    FiniteTypeContinuousModule.{u, v, w} Λ G ⥤
      (SingleObj Λ ⥤+ (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory) where
  obj M := AdditiveFunctor.of (finiteContinuousScalarFunctor Λ G M)
  map f := ObjectProperty.homMk
    { app := fun _ ↦ (finiteTypeContinuousModuleForgetAbelian Λ G).map f
      naturality := fun _ _ a ↦ by
        apply finiteContinuousAbelianHom_ext
        ext x
        exact f.hom.hom.hom.hom.hom.map_smul a x }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The abelian group underlying a finite discrete `G`-module. -/
public abbrev finiteContinuousAbelianForget :
    (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory ⥤ AddCommGrpCat.{w} :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
    Action.forget AddCommGrpCat.{w} G

/-- Taking the underlying abelian group of a finite discrete `G`-module is additive. -/
public instance finiteContinuousAbelianForget_additive :
    (finiteContinuousAbelianForget.{v, w} G).Additive where
  map_add := rfl

/-- The finite `Λ`-`G`-module attached to a finite discrete `G`-module with additive scalar
operations. -/
public def scalarActionToFiniteTypeContinuousModuleObj [Finite Λ]
    (F : SingleObj Λ ⥤+ (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory) :
    FiniteTypeContinuousModule.{u, v, w} Λ G := by
  let S := AdditiveFunctor.of (F.obj ⋙ finiteContinuousAbelianForget.{v, w} G)
  letI := scalarActionModule Λ S
  let A := F.obj.obj (SingleObj.star Λ)
  let V := (scalarActionToModule Λ).obj S
  let ρ : G →* End V :=
    { toFun := fun g ↦ End.of <| ModuleCat.ofHom
        { (A.obj.obj.obj.ρ g).asHom.hom with
          map_smul' := fun a x ↦
            (ConcreteCategory.congr_hom ((F.obj.map a).hom.hom.hom.comm g) x).symm }
      map_one' := by
        apply End.ext
        apply ModuleCat.hom_ext
        ext x
        change (A.obj.obj.obj.ρ 1).asHom.hom x = x
        simp only [map_one, End.one_asHom, AddCommGrpCat.hom_id, AddMonoidHom.coe_id]
        rfl
      map_mul' := by
        intro g h
        apply End.ext
        apply ModuleCat.hom_ext
        ext x
        change (A.obj.obj.obj.ρ (g * h)).asHom.hom x =
          (A.obj.obj.obj.ρ g).asHom.hom ((A.obj.obj.obj.ρ h).asHom.hom x)
        simp only [map_mul, End.mul_asHom, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp]
        rfl }
  let M : Action (ModuleCat.{w} Λ) G := Action.mk V ρ
  let M' : ContAction (ModuleCat.{w} Λ) G := ⟨M, by
    refine (Action.isContinuous_def _).2 ?_
    exact (Action.isContinuous_def A.obj.obj.obj).mp A.obj.obj.property⟩
  refine ⟨⟨M', by
    change DiscreteTopology (TopCat.discrete.obj V)
    infer_instance⟩, ?_⟩
  exact (moduleCat_isFG_iff_finite Λ V).mpr A.property

/-- A finite discrete `G`-module with additive scalar operations, read as a finite
`Λ`-`G`-module. -/
public def scalarActionToFiniteTypeContinuousModule [Finite Λ] :
    (SingleObj Λ ⥤+ (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory) ⥤
      FiniteTypeContinuousModule.{u, v, w} Λ G where
  obj := scalarActionToFiniteTypeContinuousModuleObj Λ G
  map {F H} f := by
    let S := AdditiveFunctor.of (F.obj ⋙ finiteContinuousAbelianForget.{v, w} G)
    let T := AdditiveFunctor.of (H.obj ⋙ finiteContinuousAbelianForget.{v, w} G)
    letI := scalarActionModule Λ S
    letI := scalarActionModule Λ T
    let a := f.hom.app (SingleObj.star Λ)
    refine ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      { hom := ModuleCat.ofHom
          { a.hom.hom.hom.hom.hom with
            map_smul' := ?_ }
        comm := ?_ }))
    · intro b x
      exact ConcreteCategory.congr_hom
        (congrArg (fun h ↦ (finiteContinuousAbelianForget.{v, w} G).map h)
          (f.hom.naturality b)) x
    · intro g
      apply ModuleCat.hom_ext
      ext x
      exact ConcreteCategory.congr_hom (a.hom.hom.hom.comm g) x
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- **A finite `Λ`-module with a continuous `G`-action is a finite discrete `G`-module with
additive scalar operations.** -/
public def finiteTypeContinuousModuleScalarActionEquivalence [Finite Λ] :
    FiniteTypeContinuousModule.{u, v, w} Λ G ≌
      (SingleObj Λ ⥤+ (ContinuousGAddCommGrp.isFinite.{v, w} G).FullSubcategory) where
  functor := finiteTypeContinuousModuleToScalarAction Λ G
  inverse := scalarActionToFiniteTypeContinuousModule Λ G
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun ⟨⟩ ↦ Iso.refl _) (by rintro ⟨⟩ ⟨⟩ a; ext; rfl)))
    (fun _ ↦ rfl)

end Scalars

end Stacks.GroupCohomology

end
