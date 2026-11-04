module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# The kernel ideal of a morphism of sheaves of rings

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`. Restriction of scalars
along `α` turns `R'` into a sheaf of `R`-modules, and `α` itself into a morphism
`unit R ⟶ (restrictScalars α).obj (unit R')` of sheaves of `R`-modules. Its sectionwise kernel is
an ideal subsheaf `I ⊆ R`, with `I(U) = ker (α_U : R(U) → R'(U))` over every object `U` of the
site.

For a closed immersion of ringed topoi `i` with structure map `i^# : O' ⟶ i_*O`, this is the
kernel ideal `I ⊆ O'` of [Stacks, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3), whose
`O'`-module quotient and annihilator are the subject of that lemma.

## Main definitions

* `SheafOfModules.unitToRestrictScalarsObjUnit`: the morphism
  `unit R ⟶ (restrictScalars α).obj (unit R')` of sheaves of `R`-modules determined by a morphism
  `α : R ⟶ R'` of sheaves of rings. It is `α` sectionwise; this is the restriction-of-scalars
  analogue of Mathlib's `SheafOfModules.unitToPushforwardObjUnit`.
* `SheafOfModules.kerIdeal`: the kernel ideal of `α`, as a `SheafOfModules.Submodule` of
  `unit R`.

## Main results

* `SheafOfModules.mem_kerIdeal` and `SheafOfModules.kerIdeal_obj`: the sections of the kernel
  ideal over an object `U` are exactly the kernel of the ring homomorphism `α_U`, the second
  statement being the equality of submodules itself and not only of their membership predicates.

## Implementation notes

The `R`-linearity of `α` is the computation `α(r * a) = α(r) * α(a) = r • α(a)`, the last step
being the definition of the `R`-action obtained by restricting scalars along `α`; this is the same
proof as Mathlib's `unitToPushforwardObjUnit`, where the ring map is instead `φ : S ⟶ f_*R` and
the module lands in `pushforward φ`. Mathlib has only the pushforward form, so the morphism is
built here.

Sheaf-theoretically there is nothing to check beyond that linearity: the kernel of a morphism of
sheaves of modules is computed sectionwise, which is `SheafOfModules.kerSubmodule`, so `kerIdeal`
is that kernel and `mem_kerIdeal` is `SheafOfModules.mem_kerSubmodule` composed with
`RingHom.mem_ker`.

`kerIdeal` is an ideal subsheaf of `R` rather than an `Ideal`-valued construction because
`SheafOfModules.Submodule` is the only ambient notion of subobject available: a submodule of
`unit R` over `U` is a submodule of `R(U)` as an `R(U)`-module, which is exactly an ideal of
`R(U)`. That is why `kerIdeal_obj` can be stated as an equality with `RingHom.ker`, whose type
`Ideal (R.obj.obj U)` is `Submodule (R.obj.obj U) (R.obj.obj U)`.

The module universe of `unit R` is forced: `unit R : SheafOfModules.{u} R` for
`R : Sheaf J RingCat.{u}`, since its sections over `U` are `R(U)` itself. So `restrictScalars` is
used at `{u}` and not at an independent module universe. The two site universes `u'` (objects)
and `v'` (morphisms) are free and independent, as is `u`.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory

universe u v' u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- The morphism `unit R ⟶ (restrictScalars α).obj (unit R')` of sheaves of `R`-modules
determined by a morphism `α : R ⟶ R'` of sheaves of rings: sectionwise it is `α` itself, which is
`R`-linear because `α (r * a) = α r * α a` and `r` acts on `R'` through `α`.

This is the restriction-of-scalars analogue of `SheafOfModules.unitToPushforwardObjUnit`. -/
noncomputable def unitToRestrictScalarsObjUnit :
    unit R ⟶ (restrictScalars.{u} α).obj (unit R') where
  val.app U := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (α.hom.app U)) (fun r ↦ by
    ext a
    exact ((α.hom.app U).hom.map_mul r a).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (α.hom.naturality f) _

@[simp]
lemma unitToRestrictScalarsObjUnit_val_app_apply {U : Cᵒᵖ} (a : R.obj.obj U) :
    (unitToRestrictScalarsObjUnit α).val.app U a = α.hom.app U a :=
  rfl

/-- The kernel ideal of a morphism `α : R ⟶ R'` of sheaves of rings: the sectionwise kernel of
`α`, as an ideal subsheaf of `R`.

For the structure map `i^# : O' ⟶ i_*O` of a closed immersion of ringed topoi this is the ideal
`I ⊆ O'` of Stacks 08M3. -/
noncomputable def kerIdeal : (unit R).Submodule :=
  kerSubmodule (unitToRestrictScalarsObjUnit α)

/-- A section of `R` over `U` lies in the kernel ideal exactly when `α` kills it. -/
lemma mem_kerIdeal (U : Cᵒᵖ) (a : R.obj.obj U) :
    a ∈ (kerIdeal α).obj U ↔ a ∈ RingHom.ker (α.hom.app U).hom := by
  rw [RingHom.mem_ker]
  exact mem_kerSubmodule (unitToRestrictScalarsObjUnit α) U a

/-- The sections of the kernel ideal over `U` are the kernel of the ring homomorphism `α_U`. -/
@[simp]
lemma kerIdeal_obj (U : Cᵒᵖ) : (kerIdeal α).obj U = RingHom.ker (α.hom.app U).hom :=
  SetLike.ext (mem_kerIdeal α U)

end SheafOfModules
