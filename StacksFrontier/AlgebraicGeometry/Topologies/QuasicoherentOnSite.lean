module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.ULift
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent sheaves of modules on a ringed site

A sheaf of modules on a site is quasi-coherent when every object of the site has a covering
on whose members the restricted module admits a global presentation, that is, is a cokernel
of a map between coproducts of copies of the structure sheaf.  This is part (6) of the
definition of the local module types in Stacks 03DL, phrased with the global notion of
Stacks 03DE(6).

## Main definitions

* `SheafOfModules.uliftForPresentation` raises the universe of the sections of a sheaf of
  modules while keeping its coefficient ring sheaf.
* `SheafOfModules.HasGlobalPresentation` expresses that a sheaf of modules is a cokernel of a
  map between coproducts of copies of the structure sheaf.
* `SheafOfModules.IsQuasicoherentOnSite` is quasi-coherence of a sheaf of modules on an
  arbitrary site.
* `SheafOfModules.isQuasicoherentOnSite` is the corresponding object property, whose full
  subcategory is the category of quasi-coherent modules on the site.

Part (7) of Stacks 03DL, the finite refinement of quasi-coherence, is
`SheafOfModules.IsFinitePresentationOnSite` in
`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite`, together with the rest of the
local module types of Stacks 03DL.

## Implementation notes

Coproducts and cokernels are expressed by their universal properties, so the predicate does
not assume a sheafification functor on the site or on any of its slices.  The site objects,
the site morphisms, the coefficient rings and the module sections have independent universes.
Before taking presentations, `uliftForPresentation` puts the module and the ring sheaf in the
common universe `max u v r m`.  That universe also bounds the families of sections and of
relations and the values of their free sheaves, so the index bounds impose no restriction on
global presentations.  The definition applies to any sheaf of rings, in particular to the
commutative structure sheaf of a ringed site.

Mathlib's `SheafOfModules.IsQuasicoherent` remains available for the existing scheme
constructions, but it requires sheafification instances on every slice.  The predicate
defined here expresses the source definition without those extra hypotheses, so that it also
applies to the fibred categories of Stacks 06WG.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- Raise the universe of the module sections without changing the coefficient rings. -/
noncomputable def uliftForPresentation (M : SheafOfModules.{m} R) : SheafOfModules.{max t m} R where
  val := {
    obj := fun X ↦ ModuleCat.of (R.obj.obj X) (ULift.{t} (M.val.obj X))
    map := fun {X Y} f ↦ ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj Y) (ULift.{t} (M.val.obj Y)))) {
      toFun := fun x ↦ ULift.up (M.val.map f x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (M.val.map f).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (M.val.map_smul f a x.down) }
    map_id := fun X ↦ by ext x; exact congrArg ULift.up (by simp)
    map_comp := fun f g ↦ by ext x; exact congrArg ULift.up (M.val.map_comp_apply f g x.down) }
  isSheaf :=
    Presheaf.isSheaf_comp_of_isSheaf J M.val.presheaf AddCommGrpCat.uliftFunctor M.isSheaf

/-- A global presentation of a sheaf of modules is a cokernel of a map between coproducts of
copies of the structure sheaf.  The coproducts and the cokernel are specified by their
universal properties, so no sheafification instance is needed. -/
noncomputable def HasGlobalPresentation (M : SheafOfModules.{m} R) : Prop :=
  ∃ (I K : Type (max u v r m))
    (P Q : SheafOfModules.{max u v r m} R)
    (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ P)
    (κ : ∀ _ : K, uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ Q),
    Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
      ∃ (a : Q ⟶ P) (b : P ⟶ uliftForPresentation.{u, v, r, m, max u v r} M)
        (hab : a ≫ b = 0), Nonempty (IsColimit (CokernelCofork.ofπ b hab))

/-- A sheaf of modules on a site is quasi-coherent when every object of the site has a
covering on whose members the restricted module admits a global presentation, as in
Stacks 03DL(6).  This predicate requires no sheafification instances. -/
@[stacks 03DL "quasi_coherent"]
class IsQuasicoherentOnSite (M : SheafOfModules.{m} R) : Prop where
  /-- Global presentations exist on a covering of each object. -/
  locally_hasGlobalPresentation : ∀ U : C,
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, HasGlobalPresentation (M.over (V i))

/-- The object property defining the category of quasi-coherent modules on a site. -/
abbrev isQuasicoherentOnSite (R : Sheaf J RingCat.{r}) :
    ObjectProperty (SheafOfModules.{m} R) := IsQuasicoherentOnSite

/-- An object of the full subcategory cut out by `isQuasicoherentOnSite` is quasi-coherent. -/
instance instIsQuasicoherentOnSiteFullSubcategoryObj
    (M : (isQuasicoherentOnSite R).FullSubcategory) :
    M.obj.IsQuasicoherentOnSite := M.property

end SheafOfModules

end
