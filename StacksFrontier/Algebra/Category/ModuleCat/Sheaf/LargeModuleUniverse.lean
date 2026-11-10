module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of modules on a topological space in a module universe above the space's

Mathlib makes `SheafOfModules.{v} R`, for `R` a sheaf of `RingCat.{u}`-valued rings on a space
in `Type u`, abelian under two hypotheses on the site — `HasSheafify` and
`WEqualsLocallyBijective` for `AddCommGrpCat.{v}` — and supplies those hypotheses only at
`v = u`. It makes the category Grothendieck abelian, hence gives it enough injectives and so
right derived functors, only at `v = u` as well
(`SheafOfModules.instIsGrothendieckAbelian`, stated for `C : Type u` small and
`R : Sheaf J RingCat.{u}`).

A sheaf of modules whose module universe exceeds the universe of the space therefore has, in
Mathlib as it stands, no abelian structure and no cohomology. That is the obstruction met by the
higher-degree comparison of Stacks 0DWR, whose statement places a sheaf of modules on
`Spec A \ V(I)` in a module universe `v` independent of the universe `u` of the ring: the
`p`-th right derived functor of its sections cannot be written down at all.

This file removes the first half of that obstruction and locates the second half exactly.

## Main results

* `Stacks.LargeModuleUniverse.hasSheafify` and
  `Stacks.LargeModuleUniverse.wEqualsLocallyBijective` — the two hypotheses of Mathlib's
  abelian structure, for abelian groups in a universe above the universe of the space. These
  are instances, so with them in scope **sheaves of modules on a space in `Type u` with module
  universe `max u v` form an abelian category**: Mathlib's abelian structure applies, and needs
  no proof beyond instance search.
* `Stacks.LargeModuleUniverse.hasFilteredColimitsOfSize` and
  `Stacks.LargeModuleUniverse.ab5OfSize`, with Mathlib's instance
  `CategoryTheory.locallySmall_self` (the morphisms already live in `max u v`) — three of the
  four fields of `CategoryTheory.IsGrothendieckAbelian.{max u v}` for that category.
* `Stacks.LargeModuleUniverse.isGrothendieckAbelian_of_hasSeparator` and
  `Stacks.LargeModuleUniverse.enoughInjectives_of_hasSeparator` — **the fourth field is the
  whole remaining gap**: a separator makes the category Grothendieck abelian and therefore
  gives it enough injectives, hence right derived functors.

## The remaining gap, and what is built here towards it

A separator for `SheafOfModules.{max u v} R` would follow, as it does at `v = u`, from one for
`PresheafOfModules.{max u v} R.obj` along the sheafification adjunction
(`CategoryTheory.HasSeparator.of_adjunction`). Mathlib's separator for presheaves of modules is
the coproduct of the free modules on the representable presheaves, and the free module functor
it uses, `PresheafOfModules.free`, has signature
`(Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R` for `R : Cᵒᵖ ⥤ RingCat.{u}`: the module universe is
tied to the *ring* universe, so neither the functor nor the separating family exists for a
module universe above it.

What is built here is that free module functor at an unrestricted module universe:

* `Stacks.LargeModuleUniverse.freeLarge` — the free `R`-module on a type whose universe may
  exceed that of `R`, with `Stacks.LargeModuleUniverse.freeLargeMk`,
  `Stacks.LargeModuleUniverse.freeLargeDesc` and the extensionality lemma for it.
* `Stacks.LargeModuleUniverse.freeLargeObj` — the presheaf of modules sending `X` to the free
  `R.obj X`-module on `F.obj X`, for a presheaf of types `F` in a universe above that of `R`.

What is *not* built is the identification of
`freeLargeObj (uliftYoneda.obj X) ⟶ M` with `M.obj (op X)` and the separating property of that
family. Mathlib proves the corresponding statements at `v = u` under
`set_option backward.isDefEq.respectTransparency.types false`, which this development does not
use: the carrier of `(ModuleCat.restrictScalars φ).obj N` is `N` only up to unfolding
`restrictScalars`, so the restriction maps of a free presheaf of modules are type-correct only
at default transparency and `rw`/`simp` cannot see through them.
`Stacks.LargeModuleUniverse.freeLargeDescRestrict` is the device used here to avoid that option
in `freeLargeObj`: it absorbs the identification into a single definition, whose `apply` lemma
is then usable by `rw`. The same device will serve for the separating family.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u v₁ u₁

namespace Stacks.LargeModuleUniverse

/-! ### Abelian structure -/

/-- Abelian groups in a universe above the universe of a space may be sheafified over that
space. Mathlib's sheafification of concrete-category-valued presheaves asks the forgetful
functor to preserve colimits over the covers of the site; those are indexed in the universe of
the space, and the forgetful functor of abelian groups preserves filtered colimits of its own
(larger) size, which is enough once the size is shrunk. -/
instance hasSheafify (Y : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max u v} := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink.{u, v, u, v} _
  infer_instance

/-- For abelian groups in a universe above the universe of a space, becoming an isomorphism
after sheafification over that space is being locally bijective. Mathlib's instance for a
concrete category asks the category's carrier universe to be exactly the universe of the site,
so it is applied here to a small model of the site in the larger universe and transported back
along the equivalence. -/
instance wEqualsLocallyBijective (Y : TopCat.{u}) :
    (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max u v} := by
  have hsm : EssentiallySmall.{max u v} (Opens Y) := inferInstance
  have h : ((equivSmallModel.{max u v} (Opens Y)).inverse.inducedTopology
      (Opens.grothendieckTopology Y)).WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {Y : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})

/-! ### Three of the four Grothendieck axioms

**Sheaves of modules on a space in `Type u` form an abelian category in every module universe
above `u`**: with the two instances above in scope, Mathlib's abelian structure for sheaves of
modules has its hypotheses, so `Abelian (SheafOfModules.{max u v} R)` is found by instance
search. No declaration here asserts that separately — an `Abelian` structure is not a
proposition, and a second instance for it would give two paths to the same structure. The
statement of `Stacks.LargeModuleUniverse.isGrothendieckAbelian_of_hasSeparator` below carries
the instance as an argument of `CategoryTheory.IsGrothendieckAbelian`, and so witnesses it. -/

/-- Sheaves of modules on a space in `Type u`, with module universe `max u v`, have filtered
colimits of size `max u v`. -/
theorem hasFilteredColimitsOfSize :
    HasFilteredColimitsOfSize.{max u v, max u v} (SheafOfModules.{max u v} R) :=
  ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩

/-- Filtered colimits of size `max u v` in presheaves of modules with module universe
`max u v` are exact: colimits there are computed on underlying presheaves of abelian groups,
where filtered colimits commute with finite limits. -/
theorem ab5OfSize_presheaf :
    AB5OfSize.{max u v, max u v} (PresheafOfModules.{max u v} R.obj) :=
  ⟨fun J _ _ ↦ ⟨⟨fun _ _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := J) ⋙ PresheafOfModules.toPresheaf R.obj) :=
      preservesLimit_of_natIso _
        (preservesColimitNatIso (PresheafOfModules.toPresheaf R.obj)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf R.obj)⟩⟩⟩⟩

/-- Filtered colimits of size `max u v` in sheaves of modules with module universe `max u v`
are exact: sheafification is left exact and preserves colimits, so the statement transfers from
presheaves of modules. -/
@[sga "4 II 6.7" "special case"]
theorem ab5OfSize : AB5OfSize.{max u v, max u v} (SheafOfModules.{max u v} R) :=
  have : AB5OfSize.{max u v, max u v} (PresheafOfModules.{max u v} R.obj) :=
    ab5OfSize_presheaf R
  ⟨fun K _ _ ↦ (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩

/-- **A separator is the only thing still missing.** With one, sheaves of modules on a space in
`Type u` with module universe `max u v` are Grothendieck abelian relative to `max u v`: the
other three axioms are the two results above and Mathlib's `CategoryTheory.locallySmall_self`. -/
theorem isGrothendieckAbelian_of_hasSeparator
    (h : HasSeparator (SheafOfModules.{max u v} R)) :
    IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} R) where
  locallySmall := inferInstance
  hasFilteredColimitsOfSize := hasFilteredColimitsOfSize R
  ab5OfSize := ab5OfSize R
  hasSeparator := h

/-- **With a separator, sheaves of modules on a space in `Type u` with module universe
`max u v` have enough injectives**, hence injective resolutions and right derived functors.
This is the statement that the higher-degree comparison of Stacks 0DWR needs in order to be
expressible at an independent module universe. -/
theorem enoughInjectives_of_hasSeparator
    (h : HasSeparator (SheafOfModules.{max u v} R)) :
    EnoughInjectives (SheafOfModules.{max u v} R) :=
  have : IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} R) :=
    isGrothendieckAbelian_of_hasSeparator R h
  IsGrothendieckAbelian.enoughInjectives.{max u v}

/-! ### The free module functor at an unrestricted module universe -/

section Free

variable (A : Type u) [Ring A]

/-- **The free `A`-module on a type whose universe may exceed the universe of `A`.** Mathlib's
`ModuleCat.free` is `Type u ⥤ ModuleCat.{u} A`; this is `Type w ⥤ ModuleCat.{max u w} A`, with
the same underlying `Finsupp`. -/
def freeLarge : Type w ⥤ ModuleCat.{max u w} A where
  obj X := ModuleCat.of A (X →₀ A)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain _ _ f)

variable {A}

/-- The generator of `Stacks.LargeModuleUniverse.freeLarge` at an element of the index type. -/
def freeLargeMk {X : Type w} (x : X) : (freeLarge.{w} A).obj X := Finsupp.single x 1

/-- Two maps out of `freeLarge A X` agree if they agree on every generator `freeLargeMk x`. -/
@[ext 1200]
lemma freeLarge_hom_ext {X : Type w} {M : ModuleCat.{max u w} A}
    {f g : (freeLarge.{w} A).obj X ⟶ M}
    (h : ∀ x : X, f (freeLargeMk x) = g (freeLargeMk x)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring (h x))

/-- The map out of a free module determined by a function on the generators. -/
def freeLargeDesc {X : Type w} {M : ModuleCat.{max u w} A} (f : X → M) :
    (freeLarge.{w} A).obj X ⟶ M :=
  ModuleCat.ofHom <| Finsupp.lift M A X f

/-- `freeLargeDesc f` sends the generator `freeLargeMk x` to `f x`. -/
@[simp]
lemma freeLargeDesc_apply {X : Type w} {M : ModuleCat.{max u w} A} (f : X → M) (x : X) :
    freeLargeDesc f (freeLargeMk x) = f x := by
  change Finsupp.lift (M : Type _) A X f (Finsupp.single x 1) = f x
  simp

/-- `Stacks.LargeModuleUniverse.freeLargeDesc` into a module whose scalars have been restricted
along `φ`.

Its purpose is to make the restriction maps of a free presheaf of modules type-correct without
unfolding `ModuleCat.restrictScalars`. The carrier of `(ModuleCat.restrictScalars φ).obj N` is
`N`, but only up to that unfolding, so a function into `N` is accepted where a function into
the restricted module is expected at default transparency and refused at the transparency
`rw` and `simp` use. Taking the identification once, here, keeps it out of every proof. -/
def freeLargeDescRestrict {B : Type u} [Ring B] (φ : A →+* B)
    {X : Type w} {N : ModuleCat.{max u w} B} (f : X → N) :
    (freeLarge.{w} A).obj X ⟶ (ModuleCat.restrictScalars φ).obj N :=
  freeLargeDesc (M := (ModuleCat.restrictScalars φ).obj N) f

/-- `freeLargeDescRestrict φ f` sends the generator `freeLargeMk x` to `f x`. -/
@[simp]
lemma freeLargeDescRestrict_apply {B : Type u} [Ring B] (φ : A →+* B)
    {X : Type w} {N : ModuleCat.{max u w} B} (f : X → N) (x : X) :
    freeLargeDescRestrict φ f (freeLargeMk x) = f x :=
  freeLargeDesc_apply (M := (ModuleCat.restrictScalars φ).obj N) f x

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The free presheaf of modules on a presheaf of types in a universe above the universe of
the ring**: it sends `X` to the free `R.obj X`-module on `F.obj X`. Mathlib's
`PresheafOfModules.freeObj` is the case where the two universes agree. -/
def freeLargeObj (F : Cᵒᵖ ⥤ Type (max u w)) : PresheafOfModules.{max u w} R where
  obj X := (freeLarge.{max u w} (R.obj X)).obj (F.obj X)
  map {X Y} f := freeLargeDescRestrict (R.map f).hom fun x ↦ freeLargeMk (F.map f x)
  map_id X := by
    ext x
    rw [freeLargeDescRestrict_apply, Functor.map_id_apply]
    rfl
  map_comp f g := by
    ext x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, freeLargeDescRestrict_apply,
      ModuleCat.restrictScalars.map_apply, freeLargeDescRestrict_apply,
      Functor.map_comp_apply, freeLargeDescRestrict_apply]
    rfl

end Free

end Stacks.LargeModuleUniverse

end
