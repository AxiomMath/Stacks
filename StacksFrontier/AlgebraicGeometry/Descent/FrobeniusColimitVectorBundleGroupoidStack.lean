module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoid
public import StacksFrontier.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import StacksFrontier.CategoryTheory.Sites.Descent.CoreDescentData

/-!
# Descent for the groupoid of Frobenius-colimit vector bundles

`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoid` builds the
maximal-subgroupoid pseudofunctor `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` by
coring `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` fibrewise, and then cuts out the
finite locally free objects.  This file supplies the comparison the two are related by — the
fibrewise inclusion of the maximal subgroupoid, as a strong transformation of pseudofunctors —
and reads off from
`CategoryTheory.Pseudofunctor.StrongTrans.isStack_of_isCoreInclusion` that **the coring inherits
the descent properties of the pseudofunctor of all Frobenius-colimit modules.**

The strong transformation is the one case of
`CategoryTheory.Pseudofunctor.catStrongTransOfIsLocallyDiscrete` where the strong naturality
constraint is an identity: Mathlib's `CategoryTheory.Functor.coreCompInclusionIso` says that
`F.core ⋙ Core.inclusion` and `Core.inclusion ⋙ F` are the same functor, by `Iso.refl`.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitModuleCoreInclusion`: the fibrewise inclusion of the
  maximal subgroupoid, as a strong transformation of pseudofunctors over the big h category.

## Main results

* `AlgebraicGeometry.isCoreInclusion_frobeniusColimitModuleCoreInclusion_app`: each component of
  that strong transformation presents a fibre of the coring as the maximal subgroupoid of the
  corresponding fibre of the pseudofunctor of all modules.
* `AlgebraicGeometry.isStackFor_frobeniusColimitModuleCorePseudofunctor` and
  `AlgebraicGeometry.isStack_frobeniusColimitModuleCorePseudofunctor`: **the coring is a stack as
  soon as the pseudofunctor of all Frobenius-colimit modules is.**

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pseudofunctor Opposite
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS

/-! ### The data of the two pseudofunctors

The objects, morphisms and structure isomorphisms of
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` and
`AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor`. -/

/-- The fibre of `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at `U` is the category
of sheaves of modules over `AlgebraicGeometry.bigHFrobeniusColimitRingSheaf` at `U`. -/
@[simp]
lemma frobeniusColimitModulePseudofunctor_obj (U : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).obj U =
      Cat.of (_root_.SheafOfModules.{u}
        (bigHFrobeniusColimitRingSheaf B S hS p hpS U.as.unop)) :=
  rfl

/-- The fibre of `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` at `U` is the
maximal subgroupoid of the category of sheaves of modules over
`AlgebraicGeometry.bigHFrobeniusColimitRingSheaf` at `U`. -/
@[simp]
lemma frobeniusColimitModuleCorePseudofunctor_obj (U : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).obj U =
      Cat.of (Core (_root_.SheafOfModules.{u}
        (bigHFrobeniusColimitRingSheaf B S hS p hpS U.as.unop))) :=
  rfl

/-- The functor of `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` along `f` is the
pullback `AlgebraicGeometry.bigHFrobeniusColimitPullback` along `f`. -/
@[simp]
lemma frobeniusColimitModulePseudofunctor_map {U V : LocallyDiscrete (BigHOver B S hS)ᵒᵖ}
    (f : U ⟶ V) :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).map f =
      (bigHFrobeniusColimitPullback B S hS p hpS f.as).toCatHom :=
  rfl

/-- The unit isomorphism of `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at `U` is
`AlgebraicGeometry.bigHFrobeniusColimitPullbackId`. -/
@[simp]
lemma frobeniusColimitModulePseudofunctor_mapId (U : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).mapId U =
      Cat.Hom.isoMk (bigHFrobeniusColimitPullbackId B S hS p hpS U.as) :=
  rfl

/-- The composition isomorphism of `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at
`f` and `g` is the inverse of `AlgebraicGeometry.bigHFrobeniusColimitPullbackComp`. -/
@[simp]
lemma frobeniusColimitModulePseudofunctor_mapComp
    {U V W : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (frobeniusColimitModulePseudofunctor B S hS p hpS).mapComp f g =
      Cat.Hom.isoMk (bigHFrobeniusColimitPullbackComp B S hS p hpS f.as g.as).symm :=
  rfl

/-- The functor of `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` along `f` is the
restriction to maximal subgroupoids of `AlgebraicGeometry.bigHFrobeniusColimitPullback`. -/
@[simp]
lemma frobeniusColimitModuleCorePseudofunctor_map {U V : LocallyDiscrete (BigHOver B S hS)ᵒᵖ}
    (f : U ⟶ V) :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).map f =
      (bigHFrobeniusColimitPullback B S hS p hpS f.as).core.toCatHom :=
  rfl

/-- The unit isomorphism of `AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` at `U`
is `AlgebraicGeometry.bigHFrobeniusColimitPullbackId` restricted to maximal subgroupoids. -/
@[simp]
lemma frobeniusColimitModuleCorePseudofunctor_mapId (U : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapId U =
      Cat.Hom.isoMk (bigHFrobeniusColimitPullbackId B S hS p hpS U.as).core :=
  rfl

/-- The component at `X` of the composition isomorphism of
`AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` at `f` and `g` is the component at
`X` of the inverse of the restriction to maximal subgroupoids of
`AlgebraicGeometry.bigHFrobeniusColimitPullbackComp`. -/
@[simp]
lemma frobeniusColimitModuleCorePseudofunctor_mapComp_hom_toNatTrans_app
    {U V W : LocallyDiscrete (BigHOver B S hS)ᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (X : (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).obj U) :
    ((frobeniusColimitModuleCorePseudofunctor B S hS p hpS).mapComp f g).hom.toNatTrans.app X =
      (bigHFrobeniusColimitPullbackComp B S hS p hpS f.as g.as).core.inv.app X :=
  rfl

/-! ### The core inclusion -/

/-- **The fibrewise inclusion of the maximal subgroupoid**, as a strong transformation from
`AlgebraicGeometry.frobeniusColimitModuleCorePseudofunctor` to
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor`.

Its component at an object `U` of the big h category over `S` is
`CategoryTheory.Core.inclusion` of the category of sheaves of `colim_F 𝒪_U`-modules, and its
strong naturality constraint is `CategoryTheory.Functor.coreCompInclusionIso`, an identity. -/
def frobeniusColimitModuleCoreInclusion :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).StrongTrans
      (frobeniusColimitModulePseudofunctor B S hS p hpS) :=
  catStrongTransOfIsLocallyDiscrete _ _
    (fun U ↦ Core.inclusion (_root_.SheafOfModules.{u}
      (bigHFrobeniusColimitRingSheaf B S hS p hpS U.as.unop)))
    (fun {_ _} f ↦
      Functor.coreCompInclusionIso (bigHFrobeniusColimitPullback B S hS p hpS f.as))
    (fun _ _ ↦ by
      dsimp only [frobeniusColimitModulePseudofunctor_obj,
        frobeniusColimitModuleCorePseudofunctor_obj, frobeniusColimitModulePseudofunctor_mapId,
        frobeniusColimitModuleCorePseudofunctor_mapId, LocallyDiscrete.id_as,
        Cat.Hom.isoMk_hom_toNatTrans_app, Functor.toCatHom_toFunctor]
      apply Core.inclusion_naturality_id)
    (fun _ _ _ ↦ by
      dsimp only [frobeniusColimitModulePseudofunctor_obj,
        frobeniusColimitModuleCorePseudofunctor_obj, frobeniusColimitModulePseudofunctor_map,
        frobeniusColimitModuleCorePseudofunctor_map,
        frobeniusColimitModulePseudofunctor_mapComp,
        frobeniusColimitModuleCorePseudofunctor_mapComp_hom_toNatTrans_app, Iso.symm_hom,
        LocallyDiscrete.comp_as, Cat.Hom.isoMk_hom_toNatTrans_app,
        Functor.toCatHom_toFunctor]
      apply Core.inclusion_naturality_comp)

/-- The component of `AlgebraicGeometry.frobeniusColimitModuleCoreInclusion` at an object is the
inclusion of the maximal subgroupoid. -/
@[simp]
lemma frobeniusColimitModuleCoreInclusion_app_toFunctor
    (a : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    ((frobeniusColimitModuleCoreInclusion B S hS p hpS).app a).toFunctor =
      Core.inclusion (_root_.SheafOfModules.{u}
        (bigHFrobeniusColimitRingSheaf B S hS p hpS a.as.unop)) :=
  rfl

/-- Each component of `AlgebraicGeometry.frobeniusColimitModuleCoreInclusion` presents a fibre of
the coring as the maximal subgroupoid of the corresponding fibre of the pseudofunctor of all
Frobenius-colimit modules.  This is `CategoryTheory.Core.isCoreInclusion_inclusion`. -/
lemma isCoreInclusion_frobeniusColimitModuleCoreInclusion_app
    (a : LocallyDiscrete (BigHOver B S hS)ᵒᵖ) :
    ((frobeniusColimitModuleCoreInclusion B S hS p hpS).app a).toFunctor.IsCoreInclusion := by
  rw [frobeniusColimitModuleCoreInclusion_app_toFunctor]
  exact Core.isCoreInclusion_inclusion _

/-- **The maximal-subgroupoid pseudofunctor of Frobenius-colimit modules is a stack for a
presieve as soon as the pseudofunctor of all Frobenius-colimit modules is.** -/
theorem isStackFor_frobeniusColimitModuleCorePseudofunctor {U : BigHOver B S hS}
    (R : Presieve U)
    (hR : (frobeniusColimitModulePseudofunctor B S hS p hpS).IsStackFor R) :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).IsStackFor R :=
  (frobeniusColimitModuleCoreInclusion B S hS p hpS).isStackFor_of_isCoreInclusion
    (isCoreInclusion_frobeniusColimitModuleCoreInclusion_app B S hS p hpS) R hR

/-- **The maximal-subgroupoid pseudofunctor of Frobenius-colimit modules is a stack as soon as
the pseudofunctor of all Frobenius-colimit modules is.** -/
theorem isStack_frobeniusColimitModuleCorePseudofunctor
    (J : GrothendieckTopology (BigHOver B S hS))
    [(frobeniusColimitModulePseudofunctor B S hS p hpS).IsStack J] :
    (frobeniusColimitModuleCorePseudofunctor B S hS p hpS).IsStack J :=
  (frobeniusColimitModuleCoreInclusion B S hS p hpS).isStack_of_isCoreInclusion
    (isCoreInclusion_frobeniusColimitModuleCoreInclusion_app B S hS p hpS) J

end AlgebraicGeometry

end
