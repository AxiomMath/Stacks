module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.StacksAttribute

/-!
# Locally bijective morphisms of sheaves of modules are isomorphisms

Let `(C, J)` be a site, let `R` be a sheaf of rings on it, and let `f : M ⟶ N` be a morphism
of sheaves of `R`-modules.  If `f` is locally injective and locally surjective then it is an
isomorphism.  Equivalently: a locally bijective morphism from a presheaf of modules into a
sheaf of modules exhibits that sheaf as the sheafification of the presheaf, so any two sheaves
of modules receiving locally bijective morphisms from the same presheaf are canonically
identified.

Mathlib proves the corresponding statement for sheaves with values in a concrete category
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`) and the universal property of
sheafification for presheaves of modules
(`CategoryTheory.PresheafOfModules.homEquivOfIsLocallyBijective`), but not the conclusion
`IsIso f` for a morphism of `SheafOfModules`.  That is what this file supplies.

## Main results

* `Stacks.SheafOfModules.isIso_of_isLocallyBijective`: a locally injective and locally
  surjective morphism of sheaves of modules is an isomorphism.
* `Stacks.SheafOfModules.isoOfIsLocallyBijective`: the resulting isomorphism, as data.
* `Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective`: if a morphism `η` from a
  presheaf of modules `P` into a sheaf `M` is locally bijective, and a morphism `h : M ⟶ N`
  of sheaves satisfies `η ≫ h.val = g` for a locally bijective `g : P ⟶ N.val`, then `h` is
  an isomorphism.  This is the form in which a consumer identifies a sheaf constructed as the
  sheafification of `P` with a sheaf `N` that merely receives a local isomorphism from `P`.

## Implementation notes

The proof is a reflection.  `SheafOfModules.toSheaf` sends a sheaf of modules to the
underlying sheaf of abelian groups, and it reflects isomorphisms: Mathlib supplies that as an
anonymous instance in `Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean`, whose
statement mentions neither `HasWeakSheafify` nor `WEqualsLocallyBijective`.  Local injectivity
and local surjectivity of a morphism of sheaves of modules are *defined* as the corresponding
properties of the underlying morphism of abelian presheaves, so they transport to
`toSheaf.map f` by `inferInstanceAs`, and Mathlib's
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` applies to the latter.

Consequently none of the statements here assumes `HasWeakSheafify`,
`GrothendieckTopology.WEqualsLocallyBijective` or any other sheafification instance, and the
universe `v` of the module sections is independent of the universe `u` of the sheaf of rings.
The only typeclass the argument needs beyond the site itself is
`GrothendieckTopology.HasSheafCompose J (CategoryTheory.forget AddCommGrpCat)`, which Mathlib
provides unconditionally from `(CategoryTheory.forget AddCommGrpCat).IsCorepresentable`; that
is why `Mathlib.Algebra.Category.Grp.ForgetCorepresentable` is imported.

Because the ring sheaf and the module universe are both free, the results apply verbatim to
the sheaves of modules on the small étale ringed site of an algebraic space,
`AlgebraicGeometry.Space.Modules`, with no `change` through the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite` and at any module universe: the Grothendieck
topology is an implicit argument recovered from the type of the sheaf of rings, so instance
search is never asked to unfold `(smallEtaleRingedSite B S hS F hF).C`.

In `isIso_of_fac_of_isLocallyBijective` the factorisation is taken as an equation on morphisms
of presheaves of modules rather than as a definitional identity, because the morphism `h` a
consumer has in hand is produced by the universal property of sheafification and so is only
characterised by that equation.

No `@[stacks]` attribute is claimed.  The mathematics is the uniqueness half of the universal
property of Tag 03CY, specialised to the case where the presheaf of rings is already a sheaf.

## References

* [Stacks Project, Tag 03CY](https://stacks.math.columbia.edu/tag/03CY)
* [Stacks Project, Section 03CX](https://stacks.math.columbia.edu/tag/03CX)
-/

@[expose] public section

open CategoryTheory

universe v v' u u'

namespace Stacks.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- A morphism of sheaves of modules which is locally injective and locally surjective is an
isomorphism. -/
theorem isIso_of_isLocallyBijective {M N : SheafOfModules.{v} R} (f : M ⟶ N)
    [PresheafOfModules.IsLocallyInjective J f.val]
    [PresheafOfModules.IsLocallySurjective J f.val] :
    IsIso f := by
  have hi : Sheaf.IsLocallyInjective ((_root_.SheafOfModules.toSheaf.{v} R).map f) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val))
  have hs : Sheaf.IsLocallySurjective ((_root_.SheafOfModules.toSheaf.{v} R).map f) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val))
  have : IsIso ((_root_.SheafOfModules.toSheaf.{v} R).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso
      ((_root_.SheafOfModules.toSheaf.{v} R).map f)).1 ⟨hi, hs⟩
  exact isIso_of_reflects_iso f (_root_.SheafOfModules.toSheaf.{v} R)

/-- The isomorphism of sheaves of modules determined by a locally bijective morphism. -/
noncomputable def isoOfIsLocallyBijective {M N : SheafOfModules.{v} R} (f : M ⟶ N)
    [PresheafOfModules.IsLocallyInjective J f.val]
    [PresheafOfModules.IsLocallySurjective J f.val] :
    M ≅ N :=
  have := isIso_of_isLocallyBijective f
  asIso f

/-- The forward morphism of `isoOfIsLocallyBijective f` is `f`. -/
@[simp]
lemma isoOfIsLocallyBijective_hom {M N : SheafOfModules.{v} R} (f : M ⟶ N)
    [PresheafOfModules.IsLocallyInjective J f.val]
    [PresheafOfModules.IsLocallySurjective J f.val] :
    (isoOfIsLocallyBijective f).hom = f :=
  rfl

/-- A sheaf of modules receiving a locally bijective morphism `η` from a presheaf of modules
`P` is the sheafification of `P`, in the following sense: if `g : P ⟶ N.val` is another
locally bijective morphism into a sheaf of modules and `h : M ⟶ N` satisfies
`η ≫ h.val = g`, then `h` is an isomorphism. -/
theorem isIso_of_fac_of_isLocallyBijective {P : PresheafOfModules.{v} R.obj}
    {M N : SheafOfModules.{v} R} {η : P ⟶ M.val} {g : P ⟶ N.val} (h : M ⟶ N)
    (fac : η ≫ h.val = g)
    [PresheafOfModules.IsLocallyInjective J η]
    [PresheafOfModules.IsLocallySurjective J η]
    [PresheafOfModules.IsLocallyInjective J g]
    [PresheafOfModules.IsLocallySurjective J g] :
    IsIso h := by
  have hfac : (PresheafOfModules.toPresheaf R.obj).map η ≫
      (PresheafOfModules.toPresheaf R.obj).map h.val =
      (PresheafOfModules.toPresheaf R.obj).map g := by
    rw [← Functor.map_comp, fac]
  have hi : PresheafOfModules.IsLocallyInjective J h.val := by
    change Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map h.val)
    rw [← Presheaf.comp_isLocallyInjective_iff J
      ((PresheafOfModules.toPresheaf R.obj).map η), hfac]
    infer_instance
  have hs : PresheafOfModules.IsLocallySurjective J h.val := by
    change Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map h.val)
    rw [← Presheaf.comp_isLocallySurjective_iff J
      ((PresheafOfModules.toPresheaf R.obj).map η), hfac]
    infer_instance
  exact isIso_of_isLocallyBijective h

end Stacks.SheafOfModules

end
