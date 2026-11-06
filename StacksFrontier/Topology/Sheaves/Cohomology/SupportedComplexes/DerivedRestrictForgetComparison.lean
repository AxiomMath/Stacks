module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HomotopyCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyExcision

/-!
# Restricting to an open subscheme and forgetting, on unbounded derived categories

Let `X` be a scheme and `U ⊆ X` an open subscheme.  Underived, "restrict the `𝒪_X`-module and
forget the module structure" *is* "forget the module structure and restrict the abelian sheaf":
`Stacks.Cohomology.SupportedComplexes.forgetRestrictCompIso` is `CategoryTheory.Iso.refl`, the
underlying abelian sheaf of `ℱ|_U` being literally `V ↦ ℱ(j(V))`.

On **unbounded** derived categories that identity is no longer available as such.  Each of the
four functors acts degreewise, through `CategoryTheory.Functor.mapDerivedCategory`, and the
degreewise action of a composite is only *canonically isomorphic* to the composite of the
degreewise actions — Mathlib has no `mapDerivedCategoryComp`.  This file supplies the resulting
comparison and the two identities that pin it down.

It is the exact analogue, for restriction to an open subscheme, of
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` for a
direct image, and is built the same way.

## Main definitions

* `Stacks.Cohomology.RestrictForgetComparison.restrictModules` and
  `Stacks.Cohomology.RestrictForgetComparison.restrictAbelian`: the two restrictions, with their
  source and target categories **ascribed** to the spellings the rest of the file needs, together
  with their exactness and additivity instances at those spellings.
* `Stacks.Cohomology.RestrictForgetComparison.restrictForgetIso`:
  `Stacks.Cohomology.SupportedComplexes.forgetRestrictCompIso` retyped at those spellings.  Still
  `CategoryTheory.Iso.refl`.
* `Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso`:
  **the comparison**, `(-)|_U^D ⋙ Φ_U^D ≅ Φ_X^D ⋙ (-)|_U^{ab,D}`, where `Φ` is the forgetful
  functor to abelian sheaves and the superscript `D` is
  `CategoryTheory.Functor.mapDerivedCategory`.
* `Stacks.Cohomology.RestrictForgetComparison.restrictForgetComplexIso` and
  `Stacks.Cohomology.RestrictForgetComparison.restrictForgetHomotopyIso`: the crossing of the two
  spellings of the composite, on cochain complexes and on homotopy categories.  Every component is
  an identity map, but the two spellings of its source and target are distinct terms.

## Main results

* `Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso_hom_app_Q`: **what pins
  the comparison down over `DerivedCategory.Q`.**  At the image of a cochain complex it is the
  canonical factorizations `CategoryTheory.Functor.mapDerivedCategoryFactors` of the four functors
  involved, with `restrictForgetComplexIso` between the two pairs.
* `Stacks.Cohomology.RestrictForgetComparison.derivedRestrictCompToSheafIso_hom_app_Qh`: **the same
  over `DerivedCategory.Qh`**, through `CategoryTheory.Functor.mapDerivedCategoryFactorsh` and
  `restrictForgetHomotopyIso`.  This is the form a consumer needs, the universal property of a
  right derived functor on an unbounded derived category being stated over `DerivedCategory.Qh`.

## Implementation notes

**Why the comparison is a composite of two.**  The isomorphism is

`(-)|_U^D ⋙ Φ_U^D ≅ ((-)|_U ⋙ Φ_U)^D = (Φ_X ⋙ (-)|_U^{ab})^D ≅ Φ_X^D ⋙ (-)|_U^{ab,D}`,

both factors being `CategoryTheory.Functor.mapDerivedCategoryCompIso`, the first at
`CategoryTheory.Iso.refl` and the second at `restrictForgetIso` inverted.  The middle equality is
*not* a step that can be skipped even though the underived comparison is `Iso.refl`: the two
composite functors, though definitionally equal, carry different `PreservesFiniteLimits` and
`PreservesFiniteColimits` instance terms, and `CategoryTheory.Functor.mapDerivedCategory` depends
on those.

Unlike in the direct-image file the comparison is *defined* by that composite rather than
compared with a separately defined one, so no analogue of `compIsoBuild_eq` is needed: both
evaluations, over `DerivedCategory.Q` and over `DerivedCategory.Qh`, are read straight off
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q` and `..._hom_app_Qh` with their
companions for the inverse.  What is left after the two readings is one inverse pair of the
canonical factorization of the composite functor, consecutive in the chain, and that is all
`chain_cancel` removes.

**Why the two evaluations keep the crossing rather than cancelling it.**  The shorter statement —
the comparison composed with the two factorizations on the right equals the two factorizations on
the left — is the shape
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_fac` has,
and it needs a type ascription identifying `Q.obj (Φ_{U} ∘ (-)|_U (P))` with
`Q.obj ((-)|_U^{ab} ∘ Φ_X (P))`.  Those two complexes *are* definitionally equal, and cheaply so,
but `DerivedCategory.Q.obj` of them is not: unification there does not use congruence and unfolds
`DerivedCategory.Q.obj` instead, which does not complete inside the heartbeat limit here.  The
evaluations are therefore stated with `restrictForgetComplexIso` and `restrictForgetHomotopyIso`
carrying the crossing as a morphism, so that every composition in the statement matches on the
nose and no ascription is needed.

**The ascribed spellings, and why they are needed.**  The category of `𝒪_U`-modules has the two
spellings `AlgebraicGeometry.Scheme.Modules ↥U` — which is `AlgebraicGeometry.Scheme.Modules`, a
`def`, hence opaque to instance search — and `SheafOfModules (structureSheafRing
↥U.toRingedSpace)`, and the category of abelian sheaves on `U` has the two spellings
`Opens.grothendieckTopology ↥U.toRingedSpace.carrier` and
`Opens.grothendieckTopology ((Opens.toTopCat X.carrier).obj U)`.  All four spellings are
definitionally equal, but instance search is keyed on the syntax: with `U.ι` restricting
`AlgebraicGeometry.Scheme.Modules X` to `AlgebraicGeometry.Scheme.Modules ↥U`, the instance
`(SheafOfModules.toSheaf R).Additive` is **not** found at that target, because unifying
`SheafOfModules ?R` with `AlgebraicGeometry.Scheme.Modules ↥U` needs the `def` unfolded.  The
remedy used here is the one recorded on
`Stacks.Cohomology.SupportedComplexes.abelianRestrictOpen`: an `abbrev` whose type is ascribed to
the spelling the use site needs, with the instances restated at that spelling by
`inferInstanceAs`, whose ascription is checked at default transparency and therefore crosses the
spellings once and for all.

**The cancellation is a helper at a variable category, applied with `exact`.**  The two spellings
of the composite functor make a chain that passes between them well typed and yet opaque to `rw`
and to `simp only`, which report that the motive is not type-correct at their transparency level.
`chain_cancel` is therefore stated at a variable category with every object implicit and every
morphism explicit, in the shape of the whole chain, and applied with `exact`, which checks up to
definitional equality.  It is the analogue of the `private` lemma of the same name in
`Stacks.Cohomology.ModulePushforwardComparison`, `private` being file-scoped.

**No `@[stacks ...]` attribute is attached to any declaration here.**  The comparison is a
component of the square of [Stacks, Tag 0G87] and states no numbered result of the source.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes (abelianRestrictOpen forgetRestrictCompIso)

universe u

namespace Stacks.Cohomology.RestrictForgetComparison

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### The formal cancellation, at a variable category -/

/-- Cancelling an inverse pair in the middle of an eight-morphism chain, at an abstract category.
The chain is the comparison unfolded through the two evaluations of
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, in which the canonical factorization of the
composite functor occurs once inverted and once not, consecutively.

Stated at a variable category with every object implicit and every morphism explicit: the objects
along the chain are definitionally equal in two spellings each, which `rw` and `simp` refuse to
identify, reporting that the target is not type-correct at their transparency level. -/
private lemma chain_cancel {C₀ : Type*} [Category* C₀] {W₀ W₁ W₂ A A₁ B₁ B₂ B₃ : C₀}
    (a : W₀ ⟶ W₁) (b : W₁ ⟶ W₂) (c : W₂ ⟶ A) (d : A ⟶ A₁) (e : A₁ ⟶ A) (hde : d ≫ e = 𝟙 A)
    (f : A ⟶ B₁) (g : B₁ ⟶ B₂) (h : B₂ ⟶ B₃) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ g ≫ h = a ≫ b ≫ c ≫ f ≫ g ≫ h := by
  rw [reassoc_of% hde]

/-! ### The two restrictions at the ascribed spellings -/

variable {X : Scheme.{u}} (U : X.Opens)

/-- **Restriction of `𝒪_X`-modules to the open subscheme `U`**, with its source and target
spelled as sheaves of modules over the structure sheaf of the underlying ringed space.  This is
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`; only the spelling of the two categories
differs, and the spelling is what the instances below — and the forgetful functor out of the
target — are keyed on. -/
abbrev restrictModules :
    _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace) :=
  Scheme.Modules.restrictFunctor U.ι

/-- Restriction of modules to an open subscheme is additive, at the ascribed spelling. -/
instance restrictModules_additive : (restrictModules U).Additive :=
  inferInstanceAs (Scheme.Modules.restrictFunctor U.ι).Additive

/-- Restriction of modules to an open subscheme is left exact, at the ascribed spelling. -/
instance restrictModules_preservesFiniteLimits : PreservesFiniteLimits (restrictModules U) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι))

/-- Restriction of modules to an open subscheme is right exact, at the ascribed spelling. -/
instance restrictModules_preservesFiniteColimits : PreservesFiniteColimits (restrictModules U) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι))

/-- **Restriction of abelian sheaves to the open subscheme `U`**, with its source spelled by the
topology of opens of the underlying space of the ringed space of `X` and its target by that of
`U`.  This is `Stacks.Cohomology.SupportedComplexes.abelianRestrictOpen U`; only the spelling of
the two categories differs, and these are the spellings the forgetful functors produce. -/
abbrev restrictAbelian :
    Sheaf (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology U.toScheme.toRingedSpace.carrier) AddCommGrpCat.{u} :=
  abelianRestrictOpen (X := X.carrier) U

/-- Restriction of abelian sheaves to an open subset is additive, at the ascribed spelling. -/
instance restrictAbelian_additive : (restrictAbelian U).Additive :=
  inferInstanceAs (abelianRestrictOpen (X := X.carrier) U).Additive

/-- Restriction of abelian sheaves to an open subset is left exact, at the ascribed spelling. -/
instance restrictAbelian_preservesFiniteLimits : PreservesFiniteLimits (restrictAbelian U) :=
  inferInstanceAs (PreservesFiniteLimits (abelianRestrictOpen (X := X.carrier) U))

/-- Restriction of abelian sheaves to an open subset is right exact, at the ascribed spelling. -/
instance restrictAbelian_preservesFiniteColimits : PreservesFiniteColimits (restrictAbelian U) :=
  inferInstanceAs (PreservesFiniteColimits (abelianRestrictOpen (X := X.carrier) U))

/-! ### The underived identity -/

/-- **Restricting a module to `U` and forgetting is forgetting and restricting the abelian
sheaf**, at the ascribed spellings.  This is
`Stacks.Cohomology.SupportedComplexes.forgetRestrictCompIso`, retyped; like it, it is
`CategoryTheory.Iso.refl`, the underlying abelian sheaf of `ℱ|_U` being literally
`V ↦ ℱ(j(V))`. -/
def restrictForgetIso :
    restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⋙ restrictAbelian U :=
  forgetRestrictCompIso U

/-! ### The comparison on unbounded derived categories -/

/-- **Restricting modules to `U` and then forgetting is forgetting and then restricting abelian
sheaves, on unbounded derived categories.**

Underived the two functors are definitionally equal — `restrictForgetIso` is
`CategoryTheory.Iso.refl` — but their degreewise actions on the derived categories are composites
of actions, and this is the canonical comparison of such a composite with the action of the
composite, in both places, with the underived identity in between. -/
def derivedRestrictCompToSheafIso :
    (restrictModules U).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
        (restrictAbelian U).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace))) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (restrictForgetIso U).symm).symm

/-! ### The crossing of the two spellings, degreewise -/

/-- **The crossing of the two spellings of the composite, on cochain complexes.**  The degreewise
action of `(-)|_U` followed by that of `Φ_U` is the degreewise action of `Φ_X` followed by that of
`(-)|_U^{ab}`: `restrictForgetIso` read through
`CategoryTheory.Functor.mapHomologicalComplexCompIso` in one direction and through the same at
`CategoryTheory.Iso.refl` in the other.  Every component is an identity map of complexes, but the
two spellings of the complex are distinct terms, which is exactly what makes this isomorphism
worth naming. -/
def restrictForgetComplexIso :
    (restrictModules U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapHomologicalComplex
            (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (restrictAbelian U).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (restrictForgetIso U).symm (ComplexShape.up ℤ)).symm

/-- **The crossing of the two spellings of the composite, on homotopy categories.**  The
homotopy-category counterpart of `restrictForgetComplexIso`, assembled from the two
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` in the same way. -/
def restrictForgetHomotopyIso :
    (restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing U.toScheme.toRingedSpace)).mapHomotopyCategory
            (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (restrictAbelian U).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso
      (Iso.refl (restrictModules U ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (restrictForgetIso U).symm (ComplexShape.up ℤ)).symm

/-! ### What pins the comparison down -/

/-- **The comparison at the image of a cochain complex.**  It is the canonical factorization
`CategoryTheory.Functor.mapDerivedCategoryFactors` of restriction, then that of the forgetful
functor on `U`, then the degreewise crossing of the two spellings, then the factorization of
restriction of abelian sheaves inverted, then that of the forgetful functor on `X` inverted.

No type ascription is needed anywhere in the statement: the crossing of the two spellings of the
composite is carried by `restrictForgetComplexIso`, not by a definitional identification of the
two spellings under `DerivedCategory.Q`, which is the one definitional check in this subject that
does not complete inside the heartbeat limit. -/
theorem derivedRestrictCompToSheafIso_hom_app_Q
    (P : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ) :
    (derivedRestrictCompToSheafIso U).hom.app (DerivedCategory.Q.obj P) =
      (show ((restrictModules U).mapDerivedCategory ⋙
            (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).obj
              (DerivedCategory.Q.obj P) ⟶
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
              (restrictAbelian U).mapDerivedCategory).obj (DerivedCategory.Q.obj P) from
      (_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory.map
          ((restrictModules U).mapDerivedCategoryFactors.hom.app P) ≫
        (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactors.hom.app
            (((restrictModules U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((restrictForgetComplexIso U).hom.app P) ≫
            (restrictAbelian U).mapDerivedCategoryFactors.inv.app
                (((_root_.SheafOfModules.toSheaf
                  (structureSheafRing X.toRingedSpace)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj P) ≫
              (restrictAbelian U).mapDerivedCategory.map
                ((_root_.SheafOfModules.toSheaf
                  (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactors.inv.app P)) := by
  simp only [derivedRestrictCompToSheafIso, restrictForgetComplexIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_Q, Functor.mapDerivedCategoryCompIso_inv_app_Q]
  exact chain_cancel _ _ _ _ _
    (Iso.inv_hom_id_app
      (restrictModules U ⋙ _root_.SheafOfModules.toSheaf
        (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactors P) _ _ _

/-- **The comparison at the image of an object of the homotopy category.**  The same five factors
as `derivedRestrictCompToSheafIso_hom_app_Q`, with
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` in place of
`CategoryTheory.Functor.mapDerivedCategoryFactors` and `restrictForgetHomotopyIso` in place of
`restrictForgetComplexIso`.

This is the form a consumer needs: the universal property of a right derived functor on an
unbounded derived category is stated over `DerivedCategory.Qh`. -/
theorem derivedRestrictCompToSheafIso_hom_app_Qh
    (J : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedRestrictCompToSheafIso U).hom.app (DerivedCategory.Qh.obj J) =
      (show ((restrictModules U).mapDerivedCategory ⋙
            (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory).obj
              (DerivedCategory.Qh.obj J) ⟶
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X.toRingedSpace)).mapDerivedCategory ⋙
              (restrictAbelian U).mapDerivedCategory).obj (DerivedCategory.Qh.obj J) from
      (_root_.SheafOfModules.toSheaf
            (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategory.map
          ((restrictModules U).mapDerivedCategoryFactorsh.hom.app J) ≫
        (_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh.hom.app
            (((restrictModules U).mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map ((restrictForgetHomotopyIso U).hom.app J) ≫
            (restrictAbelian U).mapDerivedCategoryFactorsh.inv.app
                (((_root_.SheafOfModules.toSheaf
                  (structureSheafRing X.toRingedSpace)).mapHomotopyCategory
                    (ComplexShape.up ℤ)).obj J) ≫
              (restrictAbelian U).mapDerivedCategory.map
                ((_root_.SheafOfModules.toSheaf
                    (structureSheafRing X.toRingedSpace)).mapDerivedCategoryFactorsh.inv.app
                  J)) := by
  simp only [derivedRestrictCompToSheafIso, restrictForgetHomotopyIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_Qh, Functor.mapDerivedCategoryCompIso_inv_app_Qh]
  exact chain_cancel _ _ _ _ _
    (Iso.inv_hom_id_app
      (restrictModules U ⋙ _root_.SheafOfModules.toSheaf
        (structureSheafRing U.toScheme.toRingedSpace)).mapDerivedCategoryFactorsh J) _ _ _

end Stacks.Cohomology.RestrictForgetComparison

end
