module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineDensity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.QuasicoherentCokernelsAndDirectSums
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineMemberBaseChange

/-!
# Quasi-coherent modules are cartesian on affine objects

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids and `M` a presheaf of modules over
its structure sheaf `𝒪`.  For a morphism `f : y ⟶ x` of `𝒳` the restriction map `M(x) ⟶ M(y)`
is `𝒪(x)`-linear, `𝒪(y)` being an `𝒪(x)`-algebra along `f`, so it induces the base-change
comparison `𝒪(y) ⊗_{𝒪(x)} M(x) ⟶ M(y)`.  We say `M` is *cartesian on affine objects* when this
comparison is bijective whenever `x` and `y` lie over affine schemes.  A quasi-coherent sheaf of
modules is cartesian on affine objects: this is Stacks 03DX on the affine slices, in the form
`AlgebraicGeometry.FibredSite.bijective_liftBaseChange_of_hasGlobalPresentation`.

## Main definitions

* `AlgebraicGeometry.FibredSite.restrictionLinearMap`: the restriction map as an `𝒪(x)`-linear
  map, and `AlgebraicGeometry.FibredSite.restrictionBaseChangeMap` its base-change comparison.
* `AlgebraicGeometry.FibredSite.IsCartesianOnAffines`.

## Main results

* `AlgebraicGeometry.FibredSite.isCartesianOnAffines_of_isQuasicoherentOnSite`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

omit hp in
/-- The commutative ring of sections of the structure sheaf over an object: the global functions on
the scheme it lies over.  (The fibred-in-groupoids hypothesis is carried only so that the
structure sheaf can be named.) -/
noncomputable abbrev sectionRing (_hp : p.IsFiberedInGroupoids) (x : 𝒳) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤)

variable (M : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)

/-- The module structure of the sections of `M` over the commutative ring of sections. -/
@[instance_reducible]
noncomputable def sectionModule (x : 𝒳) : Module (sectionRing hp x) (M.obj (op x)) :=
  inferInstanceAs (Module ((ringStructureSheafCore B S hS p hp .fppf).obj.obj (op x))
    (M.obj (op x)))

/-- `𝒪(y)` is an `𝒪(x)`-algebra along `f : y ⟶ x`. -/
@[instance_reducible]
noncomputable def sectionAlgebra {x y : 𝒳} (f : y ⟶ x) :
    Algebra (sectionRing hp x) (sectionRing hp y) :=
  RingHom.toAlgebra ((BigFppfOver.toScheme B S hS).map (p.map f)).appTop.hom

/-- The sections over `y` as a module over the sections of the structure sheaf over `x`, along
`f : y ⟶ x`. -/
@[instance_reducible]
noncomputable def sectionModuleAlong {x y : 𝒳} (f : y ⟶ x) :
    Module (sectionRing hp x) (M.obj (op y)) :=
  letI := sectionModule hp M y
  Module.compHom _ ((BigFppfOver.toScheme B S hS).map (p.map f)).appTop.hom

/-- The sections over `y` form a scalar tower over the sections of the structure sheaf over `x`
and over `y`, along `f : y ⟶ x`. -/
theorem sectionIsScalarTower {x y : 𝒳} (f : y ⟶ x) :
    letI := sectionModule hp M y
    letI := sectionAlgebra hp f
    letI := sectionModuleAlong hp M f
    IsScalarTower (sectionRing hp x) (sectionRing hp y) (M.obj (op y)) :=
  let := sectionModule hp M y
  let := sectionAlgebra hp f
  let := sectionModuleAlong hp M f
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The restriction map of `M` along `f : y ⟶ x`, as an `𝒪(x)`-linear map. -/
noncomputable def restrictionLinearMap {x y : 𝒳} (f : y ⟶ x) :
    letI := sectionModule hp M x
    letI := sectionModuleAlong hp M f
    M.obj (op x) →ₗ[sectionRing hp x] M.obj (op y) :=
  letI := sectionModule hp M x
  letI := sectionModuleAlong hp M f
  { toFun := M.map f.op
    map_add' := map_add _
    map_smul' := fun c m => M.map_smul f.op c m }

/-- **The base-change comparison `𝒪(y) ⊗_{𝒪(x)} M(x) ⟶ M(y)`** of the restriction map of `M`
along `f : y ⟶ x`. -/
noncomputable def restrictionBaseChangeMap {x y : 𝒳} (f : y ⟶ x) :
    letI := sectionModule hp M x
    letI := sectionModule hp M y
    letI := sectionAlgebra hp f
    sectionRing hp y ⊗[sectionRing hp x] M.obj (op x) →ₗ[sectionRing hp y] M.obj (op y) :=
  letI := sectionModule hp M x
  letI := sectionModule hp M y
  letI := sectionAlgebra hp f
  letI := sectionModuleAlong hp M f
  letI := sectionIsScalarTower hp M f
  (restrictionLinearMap hp M f).liftBaseChange (sectionRing hp y)

/-- A presheaf of modules is **cartesian on affine objects** when the base-change comparison of
every restriction map between objects lying over affine schemes is bijective. -/
def IsCartesianOnAffines : Prop :=
  ∀ ⦃x y : 𝒳⦄ (f : y ⟶ x), IsAffineOver B S hS (p.obj x) → IsAffineOver B S hS (p.obj y) →
    Function.Bijective (restrictionBaseChangeMap hp M f)

/-- **A quasi-coherent sheaf of modules is cartesian on affine objects** (Stacks 03DX on the
affine slices). -/
theorem isCartesianOnAffines_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hM : M.IsQuasicoherentOnSite) : IsCartesianOnAffines hp M.val := by
  intro x y f hx hy
  have hpres := hasGlobalPresentation_over_of_isQuasicoherentOnSite B S hS p hp M hM ⟨x, hx⟩
  let : Module (sectionRing hp x)
      ((M.over x).val.obj (op (Over.mk (𝟙 x)))) := sectionModule hp M.val x
  let : Module (sectionRing hp y)
      ((M.over x).val.obj (op (Over.mk f))) := sectionModule hp M.val y
  let := sectionAlgebra hp f
  let : Module (sectionRing hp x)
      ((M.over x).val.obj (op (Over.mk f))) := sectionModuleAlong hp M.val f
  have : IsScalarTower (sectionRing hp x) (sectionRing hp y)
      ((M.over x).val.obj (op (Over.mk f))) := sectionIsScalarTower hp M.val f
  let fA : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk (𝟙 x))) : Type u) ≃+* sectionRing hp x := RingEquiv.refl _
  let fB : (((ringStructureSheafCore B S hS p hp .fppf).over x).obj.obj
      (op (Over.mk f)) : Type u) ≃+* sectionRing hp y := RingEquiv.refl _
  let g : Over.mk f ⟶ Over.mk (𝟙 x) := Over.homMk f (by simp)
  let r : (M.over x).val.obj (op (Over.mk (𝟙 x))) →ₗ[sectionRing hp x]
      (M.over x).val.obj (op (Over.mk f)) := restrictionLinearMap hp M.val f
  exact bijective_liftBaseChange_of_hasGlobalPresentation B S hS p hp (M.over x) hpres g hx hy
    (sectionRing hp x) (sectionRing hp y) fA (fun _ _ => rfl) fB (fun _ _ => rfl) (fun _ => rfl)
    r fun _ => rfl

end AlgebraicGeometry.FibredSite
