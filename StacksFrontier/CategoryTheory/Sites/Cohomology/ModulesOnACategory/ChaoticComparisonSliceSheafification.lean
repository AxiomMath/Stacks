module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonLeray

/-!
# Sheafification commutes with restriction to a slice, as the mate of the forgetful square

Let `C` be a category with a Grothendieck topology `τ`, let `τ'` be the chaotic topology, let `O`
be a `τ`-sheaf of rings and let `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')` be the comparison morphism, so
that `ε^*` is `τ`-sheafification of presheaves of `O`-modules and `ε_*` the forgetful functor.
Fix an object `U` of `C` and write `-|_U` for restriction along `C/U ⥤ C`.

`Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso` is the isomorphism
`(P|_U)^# ≅ (P^#)|_U` at one presheaf of modules `P`.  Proved here is that it is **natural in
`P`**, and compatible with the two sheafification units, in the strongest sense available: it is
the mate of the square of right adjoints

`ε_* ⋙ (-|_U) = (-|_U) ⋙ ε_{U*}`,

which is an equality of functors (`epsilonPushforward_comp_restrictionFunctor`).  Being a mate is
exactly the unit compatibility: `CategoryTheory.unit_mateEquiv_symm` reads off

`(η_P)|_U = η_{P|_U} ≫ ε_{U*}(c_P)`

with `η` the `ε`-unit, `η'` the `ε_U`-unit and `c` the comparison, and that is the identity a
square of the two sheafifications needs.  The derived form `(L ε^*M)|_U ≅ Lε_U^*(M|_U)` follows at
once, all four functors being exact.

## Main definitions

* `Stacks.ModulesOnACategory.ChaoticComparison.sliceEpsilonPullback`: `ε_U^*`, with its domain
  spelled as the presheaves of modules on the restricted presheaf of rings.
* `Stacks.ModulesOnACategory.ChaoticComparison.sheafifyRestrictionHom` and
  `sheafifyRestrictionIso`: the comparison `(P|_U)^# ⟶ (P^#)|_U`, as the mate of the square of
  right adjoints, and the natural isomorphism it is.
* `Stacks.ModulesOnACategory.ChaoticComparison.htpySheafifyComparison` and
  `derivedSheafifyRestrictionComparison`: the square read on homotopy categories, and the
  comparison of the two derived composites it assembles into.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedSheafifyRestrictionIso`: the derived form
  `(Lε^*M)|_U ≅ Lε_U^*(M|_U)`.

## Main results

* `Stacks.ModulesOnACategory.ChaoticComparison.unit_comp_map_sheafifyRestrictionHom`: the unit
  square — the restriction of the `ε`-unit at `P` is the `ε_U`-unit at `P|_U` followed by
  `ε_{U*}` of the comparison.
* `Stacks.ModulesOnACategory.ChaoticComparison.sheafifyRestrictionHom_app`: the mate is
  `Stacks.SheafOfModules.SliceSheafification.sheafifyOverHom` at every object, which is what makes
  it invertible.
* `Stacks.ModulesOnACategory.ChaoticComparison.derivedSheafifyRestrictionIso_fac`: the defining
  property of the derived form — its value at the image of an object of the homotopy category is
  the comparison it is lifted from.

## Implementation notes

Taking the mate rather than assembling `sheafifyOverIso` into a natural transformation by hand is
not a shortcut: naturality and the unit square both come out of `CategoryTheory.mateEquiv` with no
proof, and only invertibility is left, which is `sheafifyOverIso`'s own content.  The
identification of the mate with `sheafifyOverHom` is the observation that both are the adjoint
transpose of one morphism: `sheafifyOverHom` is by definition the transpose of
`SliceSheafification.restrictedUnit`, and the mate of the identity square is the transpose of
`(-|_U)` applied to the `ε`-unit, which *is* `restrictedUnit`
(`map_unit_eq_restrictedUnit`, an equality of two spellings of one morphism).

Three places need care, all of them the same phenomenon: two definitionally equal spellings that
instance search and `rw` do not interchange.

* The sheaf of rings on `C/U` is `overRingSheaf R U` here and `R.over U` in Mathlib's
  `SheafOfModules.overFunctor` and in `SliceSheafification`.  `sliceEpsilonPullback` and
  `sheafRestriction` pin the spelling to the one restriction of *presheaves* of modules takes its
  values in, so that the composites below find their `Additive` and exactness instances, which is
  what `Functor.mapDerivedCategoryFactorsh` and `Functor.mapHomotopyCategoryCompIso` ask of each
  of their three functors.
* `Adjunction.homEquiv` of the sheafification adjunction is
  `PresheafOfModules.sheafificationHomEquiv` by `rfl`, but only at default transparency; the
  identification is made once, in `homEquiv_sheafifyOverHom`, and `rw`-ing through a goal
  containing it fails on the motive instead.
* Both implicit arguments of `PresheafOfModules.sheafificationHomEquiv` are supplied by name where
  `Equiv.apply_symm_apply` is applied.  Left to be inferred they pose a unification problem under
  a projection and exhaust the heartbeat budget — the same reason `SliceSheafification` gives for
  naming them in its own one application.

**Which localization the derived form is lifted along.**  The underived square descends to the
derived categories because all four functors are exact, and there are two ways to say that: lift
the comparison of the composites along `DerivedCategory.Q`, which describes the result at the
objects `Q.obj K` in terms of `Functor.mapDerivedCategoryFactors`, or along `DerivedCategory.Qh`,
which describes it at the objects `Qh.obj X` in terms of `Functor.mapDerivedCategoryFactorsh`.
The second is taken here.  The reason is not internal to this module: the coherence of this
isomorphism with the two sheafification units is checked against
`Stacks.DerivedFunctor.derivedAdjunction_unit_app` and
`ChaoticComparisonLeray.derivedRestrictionPushforwardIso_fac`, and both of those are stated at
`Qh.obj X`, the derived `ε`-adjunction being obtained from the adjunction induced on homotopy
categories and `Rε_*` from `totalRightDerived` along `Qh`.  Lifted along `Q` the isomorphism is
the same up to isomorphism and its defining property is in the wrong register, so the coherence
would have to cross between the two.

**Universes.** The objects and the morphisms of `C` and the section rings of `O` lie in three
independent universes `u`, `v` and `r`, and the module sections in `max u v r w` for a free `w`,
the universe at which the sheaves of modules on the site and on each slice form a Grothendieck
abelian category. `SliceSheafification.sheafifyOverIso`, which supplies the whole
content, is universe-generic.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf restrictionFunctor)
open Stacks.SheafOfModules.SliceSheafification

namespace Stacks.ModulesOnACategory.ChaoticComparison

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- `ε_U^*`, the `τ`-sheafification on the localized site, with its domain spelled as the
presheaves of modules on `overRingPresheaf R.obj U`.  That is the spelling restriction of
presheaves of modules takes its values in, and the one in which the composites below find their
instances. -/
abbrev sliceEpsilonPullback :
    PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U) ⥤
      SheafOfModules.{max u v r w} (overRingSheaf R U) :=
  epsilonPullback.{w} (overRingSheaf R U)

/-- `ε_U^*` is additive. -/
instance sliceEpsilonPullback_additive : (sliceEpsilonPullback.{w} R U).Additive :=
  epsilonPullback_additive.{w} (overRingSheaf R U)

/-- `ε_U^*` preserves finite limits. -/
instance sliceEpsilonPullback_preservesFiniteLimits :
    PreservesFiniteLimits (sliceEpsilonPullback.{w} R U) :=
  epsilonPullback_preservesFiniteLimits.{w} (overRingSheaf R U)

/-- `ε_U^*` preserves finite colimits. -/
instance sliceEpsilonPullback_preservesFiniteColimits :
    PreservesFiniteColimits (sliceEpsilonPullback.{w} R U) :=
  epsilonPullback_preservesFiniteColimits.{w} (overRingSheaf R U)

/-- **The comparison `(P|_U)^# ⟶ (P^#)|_U`,** as the mate of the square of right adjoints
`ε_* ⋙ (-|_U) = (-|_U) ⋙ ε_{U*}`.  Naturality and the unit square come with the mate; only
invertibility has content, and that is `sheafifyOverIso`. -/
def sheafifyRestrictionHom :
    restrictionFunctor.{v, u, r, max u v r w} R.obj U ⋙ sliceEpsilonPullback.{w} R U ⟶
      epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U :=
  (CategoryTheory.mateEquiv (epsilonAdjunction.{w} R)
    (epsilonAdjunction.{w} (overRingSheaf R U))
    (G := restrictionFunctor.{v, u, r, max u v r w} R.obj U) (H := sheafRestriction.{w} R U)).symm
        (𝟙 _)

/-- **The unit square.**  The restriction to `C/U` of the sheafification unit at `P` is the
sheafification unit of the localized site at `P|_U`, followed by `ε_{U*}` of the comparison.  This
is the identity that makes `sheafifyRestrictionHom` a mate. -/
theorem unit_comp_map_sheafifyRestrictionHom (P : PresheafOfModules.{max u v r w} R.obj) :
    (restrictionFunctor.{v, u, r, max u v r w} R.obj U).map ((epsilonAdjunction.{w} R).unit.app P) ≫
        𝟙 ((epsilonPushforward.{w} R ⋙ restrictionFunctor.{v, u, r, max u v r w} R.obj U).obj
          ((epsilonPullback.{w} R).obj P)) =
      (epsilonAdjunction.{w} (overRingSheaf R U)).unit.app
          ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).obj P) ≫
        (epsilonPushforward.{w} (overRingSheaf R U)).map
          ((sheafifyRestrictionHom.{w} R U).app P) :=
  CategoryTheory.unit_mateEquiv_symm (epsilonAdjunction.{w} R)
    (epsilonAdjunction.{w} (overRingSheaf R U))
    (G := restrictionFunctor.{v, u, r, max u v r w} R.obj U) (H := sheafRestriction.{w} R U) (𝟙 _) P

omit [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] in
/-- Restriction of presheaves of modules applied to the sheafification unit is
`SliceSheafification.restrictedUnit`: two spellings of one morphism. -/
theorem map_unit_eq_restrictedUnit (P : PresheafOfModules.{max u v r w} R.obj) :
    (restrictionFunctor.{v, u, r, max u v r w} R.obj U).map ((epsilonAdjunction.{w} R).unit.app P) =
      restrictedUnit.{max u v r w} R U P :=
  rfl

/-- `sheafifyOverHom` is the adjoint transpose of `SliceSheafification.restrictedUnit`, written
with the transpose of the `ε_U`-adjunction rather than with
`PresheafOfModules.sheafificationHomEquiv`. -/
theorem homEquiv_sheafifyOverHom (P : PresheafOfModules.{max u v r w} R.obj) :
    (epsilonAdjunction.{w} (overRingSheaf R U)).homEquiv
        ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).obj P)
        ((epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U).obj P)
        (sheafifyOverHom.{max u v r w} R U P) =
      restrictedUnit.{max u v r w} R U P := by
  have e1 : (epsilonAdjunction.{w} (overRingSheaf R U)).homEquiv
        ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).obj P)
        ((epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U).obj P)
        (sheafifyOverHom.{max u v r w} R U P) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 (R.over U).obj)
        (sheafifyOverHom.{max u v r w} R U P) := rfl
  rw [e1]
  exact Equiv.apply_symm_apply
    (PresheafOfModules.sheafificationHomEquiv
      (P := (presheafOverFunctor.{max u v r w} R U).obj P)
      (F := ((PresheafOfModules.sheafification.{max u v r w} (𝟙 R.obj)).obj P).over U)
      (𝟙 (R.over U).obj))
    (restrictedUnit.{max u v r w} R U P)

/-- **The mate is `sheafifyOverHom`.**  Both are the adjoint transpose of
`SliceSheafification.restrictedUnit`: for the mate that is the unit square, for `sheafifyOverHom`
it is its definition. -/
theorem sheafifyRestrictionHom_app (P : PresheafOfModules.{max u v r w} R.obj) :
    (sheafifyRestrictionHom.{w} R U).app P = sheafifyOverHom.{max u v r w} R U P :=
  ((epsilonAdjunction.{w} (overRingSheaf R U)).homEquiv _ _).injective <|
    (Adjunction.homEquiv_unit _ _ _ _).trans
      (((unit_comp_map_sheafifyRestrictionHom.{w} R U P).symm.trans (Category.comp_id _)).trans
        ((map_unit_eq_restrictedUnit.{w} R U P).trans
          (homEquiv_sheafifyOverHom.{w} R U P).symm))

/-- The comparison is invertible at every presheaf of modules, being `sheafifyOverHom`. -/
instance isIso_sheafifyRestrictionHom_app (P : PresheafOfModules.{max u v r w} R.obj) :
    IsIso ((sheafifyRestrictionHom.{w} R U).app P) := by
  rw [sheafifyRestrictionHom_app]
  exact isIso_sheafifyOverHom.{max u v r w} R U P

/-- **Sheafification commutes with restriction to the localized site, naturally:**
`(P|_U)^# ≅ (P^#)|_U` as an isomorphism of functors. -/
def sheafifyRestrictionIso :
    restrictionFunctor.{v, u, r, max u v r w} R.obj U ⋙ sliceEpsilonPullback.{w} R U ≅
      epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U :=
  NatIso.ofComponents (fun P => asIso ((sheafifyRestrictionHom.{w} R U).app P))
    (fun f => (sheafifyRestrictionHom.{w} R U).naturality f)

/-- The sheafification square read on homotopy categories: `(P|_U)^# ≅ (P^#)|_U` applied
degreewise to a complex, up to homotopy.  The two underived composites are the ones
`sheafifyRestrictionIso` joins, and the second comparison is there only to split
`(ε^* ⋙ (-|_U))^h` into `(ε^*)^h ⋙ ((-|_U))^h`; its components are identities. -/
def htpySheafifyComparison :
    (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (sliceEpsilonPullback.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (sheafRestriction.{w} R U).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (sheafifyRestrictionIso.{w} R U) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (epsilonPullback.{w} R ⋙ sheafRestriction.{w} R U)) (ComplexShape.up ℤ)).symm

/-- The comparison of the two derived composites read on the homotopy category, out of which the
derived square is lifted: the four `Functor.mapDerivedCategoryFactorsh` of `ε^*`, `ε_U^*` and the
two restrictions, with `htpySheafifyComparison` in the middle. -/
def derivedSheafifyRestrictionComparison :
    DerivedCategory.Qh ⋙ (derivedRestriction.{w} R.obj U ⋙
        (sliceEpsilonPullback.{w} R U).mapDerivedCategory) ≅
      DerivedCategory.Qh ⋙ ((epsilonPullback.{w} R).mapDerivedCategory ⋙
        (sheafRestriction.{w} R U).mapDerivedCategory) :=
  Functor.isoWhiskerRight
      (restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh
      (sliceEpsilonPullback.{w} R U).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft
      ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory (ComplexShape.up ℤ))
      (sliceEpsilonPullback.{w} R U).mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (htpySheafifyComparison.{w} R U) DerivedCategory.Qh ≪≫
    (Functor.isoWhiskerLeft
      ((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ))
      (sheafRestriction.{w} R U).mapDerivedCategoryFactorsh).symm ≪≫
    (Functor.isoWhiskerRight (epsilonPullback.{w} R).mapDerivedCategoryFactorsh
      (sheafRestriction.{w} R U).mapDerivedCategory).symm

/-- The comparison written out at an object: the four `Functor.mapDerivedCategoryFactorsh` in
order, with the homotopy-category sheafification square in the middle. -/
theorem derivedSheafifyRestrictionComparison_hom_app
    (X : HomotopyCategory (PresheafOfModules.{max u v r w} R.obj) (ComplexShape.up ℤ)) :
    (derivedSheafifyRestrictionComparison.{w} R U).hom.app X =
      (sliceEpsilonPullback.{w} R U).mapDerivedCategory.map
          ((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapDerivedCategoryFactorsh.hom.app
              X) ≫
        (sliceEpsilonPullback.{w} R U).mapDerivedCategoryFactorsh.hom.app
          (((restrictionFunctor.{v, u, r, max u v r w} R.obj U).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((htpySheafifyComparison.{w} R U).hom.app X) ≫
        (sheafRestriction.{w} R U).mapDerivedCategoryFactorsh.inv.app
          (((epsilonPullback.{w} R).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
        (sheafRestriction.{w} R U).mapDerivedCategory.map
          ((epsilonPullback.{w} R).mapDerivedCategoryFactorsh.inv.app X) :=
  rfl

/-- **The derived form:** `(Lε^*M)|_U ≅ Lε_U^*(M|_U)`.  All four functors are exact, so each
descends degreewise to the derived categories; the isomorphism is lifted along
`DerivedCategory.Qh`, which is a localization functor for the quasi-isomorphisms of the homotopy
category, from `derivedSheafifyRestrictionComparison`.

Lifting along `Qh` rather than along `DerivedCategory.Q` is what makes
`derivedSheafifyRestrictionIso_fac` available in the register of
`Stacks.DerivedFunctor.derivedAdjunction_unit_app` and of
`ChaoticComparisonLeray.derivedRestrictionPushforwardIso_fac`, which is the register in which the
coherence of this isomorphism with the two sheafification units is checked. -/
def derivedSheafifyRestrictionIso :
    derivedRestriction.{w} R.obj U ⋙ (sliceEpsilonPullback.{w} R U).mapDerivedCategory ≅
      (epsilonPullback.{w} R).mapDerivedCategory ⋙
        (sheafRestriction.{w} R U).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (PresheafOfModules.{max u v r w} R.obj) (ComplexShape.up ℤ))
    (DerivedCategory.Qh ⋙ (derivedRestriction.{w} R.obj U ⋙
      (sliceEpsilonPullback.{w} R U).mapDerivedCategory))
    (DerivedCategory.Qh ⋙ ((epsilonPullback.{w} R).mapDerivedCategory ⋙
      (sheafRestriction.{w} R U).mapDerivedCategory))
    _ _ (derivedSheafifyRestrictionComparison.{w} R U)

/-- **The defining property of `derivedSheafifyRestrictionIso`:** its value at the image of an
object of the homotopy category is the comparison it was lifted from.  This is the handle the
coherence with the two sheafification units runs on. -/
theorem derivedSheafifyRestrictionIso_fac
    (X : HomotopyCategory (PresheafOfModules.{max u v r w} R.obj) (ComplexShape.up ℤ)) :
    (derivedSheafifyRestrictionIso.{w} R U).hom.app (DerivedCategory.Qh.obj X) =
      (derivedSheafifyRestrictionComparison.{w} R U).hom.app X := by
  simp [derivedSheafifyRestrictionIso]

end Stacks.ModulesOnACategory.ChaoticComparison

end
