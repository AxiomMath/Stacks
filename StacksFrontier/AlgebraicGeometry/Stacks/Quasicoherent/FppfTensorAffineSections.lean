module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafificationAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom

/-!
# Sections over affine objects of the tensor product of modules cartesian along flat maps

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F`, `G` be sheaves of
modules on the associated fppf site, with module sections in the universe `u` of the schemes,
both *cartesian along flat morphisms of affines*: for every arrow `z ⟶ x` of `𝒳` between
objects lying over affine schemes whose image in schemes is flat, the base-change comparisons
`Γ(z, 𝒪) ⊗_{Γ(x, 𝒪)} F(x) ⟶ F(z)` and `Γ(z, 𝒪) ⊗_{Γ(x, 𝒪)} G(x) ⟶ G(z)` are isomorphisms.
Let `F ⊗_{𝒪} G` be their tensor product in `Mod(𝒪_𝒳)`, the fppf sheafification of the
objectwise tensor product (`Stacks.SheafOfModules.Tensor.sheafTensor`).  Then

* for every object `x` lying over an affine scheme, the sheafification unit
  `F(x) ⊗_{𝒪(x)} G(x) ⟶ (F ⊗_{𝒪} G)(x)` is bijective
  (`AlgebraicGeometry.FibredSite.bijective_sheafTensor_unit_app_of_isAffine`), and
* `F ⊗_{𝒪} G` is again cartesian along flat morphisms of affines
  (`AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_sheafTensor`).

## Main results

* `AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_tensorObj_of_flat`: the objectwise
  tensor product of two presheaves of modules cartesian along flat morphisms of affines is
  cartesian along flat morphisms of affines.
* `AlgebraicGeometry.FibredSite.bijective_sheafTensor_unit_app_of_isAffine`: the sheafification
  unit `F(x) ⊗_{𝒪(x)} G(x) ⟶ (F ⊗_{𝒪} G)(x)` is bijective over affine objects.
* `AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_sheafTensor`: `F ⊗_{𝒪} G` is
  cartesian along flat morphisms of affines.

## References

* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}] in
include hp in
/-- **The objectwise tensor product of two presheaves of modules cartesian along flat morphisms
of affines is cartesian along flat morphisms of affines.** -/
theorem isIso_restrictionBaseChange_tensorObj_of_flat
    (F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf).obj)
    (hF : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) F φ.op))
    (hG : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) G φ.op))
    {z x : 𝒳} (φ : z ⟶ x) (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp .fppf).obj)
      (PresheafOfModules.tensorObj (O := (structureSheaf B S hS p hp .fppf).obj) F G) φ.op) := by
  have := hF φ hz hx hφ
  have := hG φ hz hx hφ
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_tensorObj
    (R := (structureSheaf B S hS p hp .fppf).obj) F G φ.op

include hp in
/-- **The sections over an object lying over an affine scheme of the tensor product in
`Mod(𝒪_𝒳)` of two modules cartesian along flat morphisms of affines are the tensor product of
their sections**: the sheafification unit `F(x) ⊗_{𝒪(x)} G(x) ⟶ (F ⊗_{𝒪} G)(x)` is
bijective. -/
theorem bijective_sheafTensor_unit_app_of_isAffine
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) F.val φ.op))
    (hG : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) G.val φ.op))
    {x : 𝒳} (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x))) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringStructureSheafCore B S hS p hp .fppf).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (structureSheaf B S hS p hp .fppf).obj) F.val
          G.val)).app (op x)) :=
  bijective_sheafificationAdjunction_unit_app_of_isAffine_of_flat B S hS p hp _
    (fun φ ↦ isIso_restrictionBaseChange_tensorObj_of_flat B S hS p hp F.val G.val hF hG φ) hx

include hp in
/-- **The tensor product in `Mod(𝒪_𝒳)` of two modules cartesian along flat morphisms of affines
is cartesian along flat morphisms of affines.** -/
theorem isIso_restrictionBaseChange_sheafTensor
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hF : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) F.val φ.op))
    (hG : ∀ {z x : 𝒳} (φ : z ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) →
      Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)) →
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) G.val φ.op))
    {z x : 𝒳} (φ : z ⟶ x) (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)))
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (structureSheaf B S hS p hp .fppf).obj)
      ((PresheafOfModules.sheafification (𝟙 (ringStructureSheafCore B S hS p hp .fppf).obj)).obj
        (PresheafOfModules.tensorObj (O := (structureSheaf B S hS p hp .fppf).obj) F.val
          G.val)).val φ.op) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringStructureSheafCore B S hS p hp .fppf).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (structureSheaf B S hS p hp .fppf).obj) F.val G.val)
  have hη : ∀ {y : 𝒳}, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) →
      IsIso (η.app (op y)) := fun hy ↦ (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_sheafTensor_unit_app_of_isAffine B S hS p hp F G hF hG hy)
  have h1 := @Functor.map_isIso _ _ _ _ _ _ (ModuleCat.extendScalars
    ((structureSheaf B S hS p hp .fppf).obj.map φ.op).hom) _ (hη hx)
  have h2 : IsIso ((ModuleCat.extendScalars
      ((structureSheaf B S hS p hp .fppf).obj.map φ.op).hom).map (η.app (op x)) ≫
      Stacks.PresheafOfModules.restrictionBaseChange
        (R := (structureSheaf B S hS p hp .fppf).obj) _ φ.op) := by
    rw [Stacks.PresheafOfModules.restrictionBaseChange_naturality
      (R := (structureSheaf B S hS p hp .fppf).obj) η φ.op]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_restrictionBaseChange_tensorObj_of_flat B S hS p hp F.val G.val hF hG φ hz hx hφ)
      (hη hz)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h2

end AlgebraicGeometry.FibredSite
