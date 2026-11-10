module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution

/-!
# The absolute Čech coefficient presheaf with arbitrary module coefficients

`Stacks.CechSiteChange.absoluteCechOpensPresheafIsoApp` identifies the coefficient presheaf

`U ↦ (U.ι)_* (U.ι)^* ℱ`

of [Stacks, Tag 01XL] over the site of open sets of a scheme `X` with the Čech diagram
`U ↦ ℱ(· ⊓ U)` of [Stacks, Tag 02FU], but only for a **quasi-coherent** `ℱ`:  the presheaf
`Stacks.CechSiteChange.absoluteCechOpensPresheaf` is a functor on the quasi-coherent full
subcategory.

Quasi-coherence plays no role in that identification.  Both the comparison at a fixed open set,
`Stacks.Tag01XLCoefficientIso.pullbackPushforwardInfIso`, and its naturality in the open set,
`Stacks.CechSiteChange.pullbackPushforwardInfIso_naturality`, are already stated for an arbitrary
`𝒪_X`-module.  This file removes the restriction, which is what the comparison

`𝓚⁼(K, f, ℱ) ⟶ Rf_*ℱ`

of [Stacks, Tag 01XN] needs:  that comparison is obtained from an injective resolution of `ℱ`, and
an injective `𝒪_X`-module is not quasi-coherent.

## Main definitions

* `absOpensPresheafAll`:  the coefficient presheaf of [Stacks, Tag 01XL] over the site of open sets
  of `X`, as a functor of an arbitrary `𝒪_X`-module.
* `absOpensPresheafAllObjIso`:  **the coefficient presheaf is the Čech diagram of
  [Stacks, Tag 02FU]** at an arbitrary `𝒪_X`-module, naturally in the open set.

## Main results

* `absOpensPresheafAll_map_eq`:  the restriction maps of the coefficient presheaf are the canonical
  comparisons `Stacks.AlgebraicGeometry.RelativeCech.relativeUnit'`.

## Implementation notes

The identification of the restriction maps is factored into two steps, `absOpensPresheafAll_map`
and `relativeMonad_map_opensOver_app`, for the same reason the quasi-coherent version is:  the
single `rfl` does not fit in the kernel's budget while each step checks immediately.  The second
step passes to components with `CategoryTheory.NatTrans.congr_app` rather than with a bare
`congrArg`:  a `congrArg` on the equality of natural transformations exhausts the budget
here where `NatTrans.congr_app` does not.

This module is deliberately kept at the import closure of
`StacksFrontier.AlgebraicGeometry.CechSiteChange.Resolution`.  The cost of the definitional
unfoldings
above depends on what is in scope:  the same `rfl`s are rejected once the import closure of the
relative hypercovering complex is added, so the statements that need them are proved here and only
used downstream.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 01XN](https://stacks.math.columbia.edu/tag/01XN)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeCech
open Stacks.Tag01XLCoefficientIso

universe u

namespace Stacks.CechSiteChange

variable {X : Scheme.{u}}

/-- **The coefficient presheaf of [Stacks, Tag 01XL] over the site of open sets of `X`, with
arbitrary module coefficients**:  an open `U` of `X` goes to the `𝒪_X`-module `(U.ι)_* (U.ι)^* M`.
This is `Stacks.CechSiteChange.absoluteCechOpensPresheaf` with the restriction to the
quasi-coherent full subcategory removed. -/
noncomputable def absOpensPresheafAll (X : Scheme.{u}) :
    X.Modules ⥤ ((X.Opens)ᵒᵖ ⥤ X.Modules) :=
  (relativeMonad X).flip ⋙
    (Functor.whiskeringLeft (X.Opens)ᵒᵖ (Over X)ᵒᵖ X.Modules).obj (opensOver X).op

/-- The value of the coefficient presheaf is the direct image of the inverse image along the
inclusion of the open set. -/
theorem absOpensPresheafAll_obj_obj (M : X.Modules) (U : X.Opens) :
    ((absOpensPresheafAll X).obj M).obj (op U) =
      (pushforward (Scheme.Opens.ι (X := X) U)).obj
        ((Scheme.Modules.pullback (Scheme.Opens.ι (X := X) U)).obj M) :=
  rfl

/-- The restriction maps of the coefficient presheaf are the components of the presheaf of
monads. -/
theorem absOpensPresheafAll_map (M : X.Modules) {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((absOpensPresheafAll X).obj M).map g =
      ((relativeMonad X).map ((opensOver X).op.map g)).app M :=
  rfl

/-- The presheaf of monads along an inclusion of open sets, at one module:  the canonical
restriction map of the coefficient system. -/
theorem relativeMonad_map_opensOver_app (M : X.Modules) {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((relativeMonad X).map ((opensOver X).op.map g)).app M =
      (relativeUnit' (X.homOfLE (leOfHom g.unop))
        (Scheme.Opens.ι (X := X) A.unop) (Scheme.Opens.ι (X := X) B.unop)
        (X.homOfLE_ι (leOfHom g.unop))).app M :=
  NatTrans.congr_app (relativeMonad_map_opensOver X g) M

/-- **The restriction map of the coefficient presheaf is the canonical comparison
`relativeUnit'`.** -/
theorem absOpensPresheafAll_map_eq (M : X.Modules) {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((absOpensPresheafAll X).obj M).map g =
      (relativeUnit' (X.homOfLE (leOfHom g.unop))
        (Scheme.Opens.ι (X := X) A.unop) (Scheme.Opens.ι (X := X) B.unop)
        (X.homOfLE_ι (leOfHom g.unop))).app M :=
  (absOpensPresheafAll_map M g).trans (relativeMonad_map_opensOver_app M g)

/-- The naturality in the open set of the coefficient comparison, in the form the isomorphism of
presheaves consumes. -/
theorem absOpensPresheafAllObjIso_naturality (M : X.Modules) {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((absOpensPresheafAll X).obj M).map g ≫ ((pullbackPushforwardInfIso X B.unop).app M).hom =
      ((pullbackPushforwardInfIso X A.unop).app M).hom ≫
        ((cechDiagramOpens X).obj M).map g :=
  (congrArg (fun z ↦ z ≫ ((pullbackPushforwardInfIso X B.unop).app M).hom)
      (absOpensPresheafAll_map_eq M g)).trans
    ((pullbackPushforwardInfIso_naturality X (leOfHom g.unop) M).trans
      (congrArg (fun z ↦ ((pullbackPushforwardInfIso X A.unop).app M).hom ≫
          ((cechDiagramOpens X).obj M).map z)
        (Subsingleton.elim (homOfLE (leOfHom g.unop)).op g)))

/-- **At an arbitrary `𝒪_X`-module, the coefficient presheaf of [Stacks, Tag 01XL] over the site of
open sets is the Čech diagram of [Stacks, Tag 02FU]**:  `(U.ι)_* (U.ι)^* M ≅ M(· ⊓ U)`, naturally
in the open set `U`.

This is the all-modules form of `Stacks.CechSiteChange.absoluteCechOpensPresheafIsoApp`. -/
noncomputable def absOpensPresheafAllObjIso (X : Scheme.{u}) (M : X.Modules) :
    (absOpensPresheafAll X).obj M ≅ (cechDiagramOpens X).obj M :=
  NatIso.ofComponents (fun A ↦ (pullbackPushforwardInfIso X A.unop).app M)
    (fun {_ _} g ↦ absOpensPresheafAllObjIso_naturality M g)

end Stacks.CechSiteChange

end
