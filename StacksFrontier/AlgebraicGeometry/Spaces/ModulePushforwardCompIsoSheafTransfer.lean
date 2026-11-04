module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart

/-!
# The composition comparison of Stacks 03LU under the sheaf-of-sets functor

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, and write `𝒱` for `CategoryTheory.Sheaf.moduleSheafFunctor` at the structure
sheaf.  Stacks 03LU gives the comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of
`𝒪`-modules, `AlgebraicGeometry.Space.modulePushforwardCompIso`; Stacks 03G2, part (3) gives the
corresponding comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` for sheaves of
*sets* on the small étale sites.  Both are maps `g_*(f_*F) ⟶ (f ≫ g)_*F`, the first of
`𝒪_Z`-modules and the second of sheaves of sets, and this file proves that the first is the
second:

`𝒱.map ((modulePushforwardCompIso f g).hom.app F)
  = (smallToposMorphismTypeU_comp f g).hom.app (𝒱F)`.

The mathematical content is already in the library, as
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean`), which carries
`@[stacks 03LU]` for exactly this clause — but stated for the *transported* form that
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` identifies the comparison
with, namely `CategoryTheory.Functor.compIsoCongr` of three functor equalities.  What this file
adds is the comparison in the spelling the arrows of Stacks 03M8 are written in, where
`AlgebraicGeometry.Space.modulePushforwardCompIso` appears under its own name.  Getting from the
one to the other is a single rewrite, and it is a rewrite the *kernel* does not survive when it
is performed on sheaves; see the implementation notes.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`: the comparison of
  Stacks 03LU and the geometric comparison of Stacks 03G2, part (3), agree on every local
  section.  This is the form the identification is affordable in.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`: **the
  comparison of Stacks 03LU is the geometric comparison of Stacks 03G2, part (3), on underlying
  sheaves of sets**, with `AlgebraicGeometry.Space.modulePushforwardCompIso` named as such.
* `AlgebraicGeometry.Space.moduleSheafFunctor_mapIso_modulePushforwardCompIso_app` is the same
  as an equality of *isomorphisms* of sheaves of sets, and
  `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_inv_app` is its
  inverse half — the direction `AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow` and
  `AlgebraicGeometry.Space.chartDirectImageParallelArrow` are built from.

## Implementation notes

**What the kernel would not do.**  The obvious route is to rewrite the comparison into its
transported form with `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq` under `𝒱`,
that is to take

`(congrArg 𝒱.map (modulePushforwardCompIso_hom_app_eq f g F)).trans
  (moduleSheafFunctor_map_compIsoCongr_hom_app f g F)`.

That term *elaborates* and is then rejected: the kernel reports

`error: (kernel) deterministic timeout`

on the lifted auxiliary proof.  The transported form is `CategoryTheory.Functor.compIsoCongr` of
three equalities of functors, so it carries `eqToHom` transports whose reduction the kernel has
to perform inside a `Hom` type of sheaves of modules on the small étale site, and that reduction
does not come back.  Raising a limit is not available in this repository, and a kernel timeout is
not a limit that could be raised in any case.

**The vocabulary that dissolves it**, in the manner of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardTriangle.lean`: do the rewrite on a single
*local section* instead of on sheaves.
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` below performs it at a
section `z` over an object `W` of the small étale site, where the
`congrArg` is taken over `fun m ↦ m.val.app W z` — a function into a *type* of sections rather
than into a `Hom` of sheaves — and the identification the kernel then has to check is between
two elements of one type.  That goes through, and
`CategoryTheory.Sheaf.hom_ext_sections` assembles the sections back into the equation of sheaf
morphisms, which is the statement wanted.  This is the same manoeuvre the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean` record for the substitution
chain of Stacks 05Z7 ("the two halves are glued on sections ... where the identification needed
is between two types rather than between two sheaves of types"), and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean` carries out its special
case at the structure sheaf.

The inverse half is not proved a second time: the two sides of the comparison are assembled into
an equality of isomorphisms by `CategoryTheory.Iso.ext`, and the inverses are then equal by
`congrArg`, because `CategoryTheory.Functor.mapIso` and `CategoryTheory.Iso.app` take their
inverse from the inverse of their argument.

Nothing here raises a compiler limit or disables a linter.

## What is not done

The consumer of this comparison is the module-level reading of the sequence of Stacks 03M8 that
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` records as
waiting on it: that the sheaf of sets underlying
`AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` is
`AlgebraicGeometry.Space.chartDirectImageUnitArrow`, and likewise for the two parallel arrows.
That step is **not** reached here, and the obstruction is not the comparison above but the
*other* factor of those arrows.  The first
arrow of the sequence splits as the direct image along `f` of the unit at `τ` followed by the
comparison above, and the second factor is discharged, while merely *stating* the clause for
the first factor,

`𝒱.map ((modulePushforward f).map ((etaleModulePullbackAdjunction τ hτ).unit.app F)) =
  (smallEtaleDirectImage f).map ((smallEtaleSetRestrictionAdjunction τ hτ).unit.app (𝒱F))`,

reports

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached`

in the *statement* — the two sides' common `Hom` type has to be found by reconciling
`𝒱((modulePushforward τ).obj (F|_U))` with
`(smallEtaleSetRestriction τ hτ ⋙ smallEtaleDirectImage τ).obj (𝒱F)` inside the implicit object
arguments of `(smallEtaleDirectImage f).map`, and that reconciliation diverges.  Assembling the
whole first arrow in one `show`, with both factors written out, reports
`(deterministic) timeout at 'isDefEq'` for the same reason, and the section-level form of either
— the manoeuvre that dissolved the comparison above — diverges in the same way, because the
reconciliation then moves into the *result* type of the two sides.

That factor is no longer open:
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleChartUnitArrowSheafTransfer.lean` names the set-level
unit with its declared type in the `𝒱`-spelling, which spends the reconciliation once in a
definition's body and makes the clause an ordinary `congrArg`.  With both factors read on
underlying sheaves of sets, what still separates their composite from
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is one spelling identification of the
*composite*; that file's "What is not done" measures it and names the vocabulary it would need.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The comparison on a local section -/

/-- **The comparison `g_*(f_*F) ⟶ (f ≫ g)_*F` of Stacks 03LU and the geometric comparison of
Stacks 03G2, part (3), agree on every local section** of the small étale site of `Z`.

This is `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq`, which rewrites the
comparison into its transported `CategoryTheory.Functor.compIsoCongr` form, followed by
`AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`, which is that form's
identification with the geometric comparison.  Both steps are taken on the section `z`: the
`congrArg` is over a function into a type of sections, and not over one into a `Hom` type of
sheaves of modules, which is what makes the identification affordable — see this file's
implementation notes. -/
theorem modulePushforwardCompIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F)).val.obj W) :
    ((modulePushforwardCompIso B S hS f g).hom.app F).val.app W z =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)).hom.app W z :=
  (congrArg (fun m : (modulePushforward B S hS g).obj ((modulePushforward B S hS f).obj F) ⟶
      (modulePushforward B S hS (f ≫ g)).obj F ↦ m.val.app W z)
    (modulePushforwardCompIso_hom_app_eq B S hS f g F)).trans
    (Sheaf.hom_congr_app_apply (moduleSheafFunctor_map_compIsoCongr_hom_app B S hS f g F) W z)

/-! ### The comparison on underlying sheaves of sets -/

/-- **Stacks 03LU.**  The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules
is, on underlying sheaves of sets, the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3).

This is `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app` with the
comparison named as `AlgebraicGeometry.Space.modulePushforwardCompIso` rather than through the
transported form of `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr`, which is
the spelling the arrows of the sequence of Stacks 03M8 are written in.  It is the equality of
sections of `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app`, reassembled by
`CategoryTheory.Sheaf.hom_ext_sections`; performing the renaming on sheaves instead exceeds the
kernel's budget, as this file's implementation notes record. -/
theorem moduleSheafFunctor_map_modulePushforwardCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforwardCompIso B S hS f g).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  Sheaf.hom_ext_sections fun W z ↦
    modulePushforwardCompIso_hom_app_val_app B S hS f g F W z

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` as an
equality of *isomorphisms* of sheaves of sets: the image under the sheaf-of-sets functor of the
comparison of Stacks 03LU at a module is the geometric comparison of Stacks 03G2, part (3), at
the underlying sheaf of sets.

An isomorphism is determined by its `hom` (`CategoryTheory.Iso.ext`), so this carries no content
beyond the previous result; it is stated because it is what gives the inverse half. -/
theorem moduleSheafFunctor_mapIso_modulePushforwardCompIso_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).mapIso
        ((modulePushforwardCompIso B S hS f g).app F) =
      (smallToposMorphismTypeU_comp B S hS f g).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  Iso.ext (moduleSheafFunctor_map_modulePushforwardCompIso_hom_app B S hS f g F)

/-- **The inverse half of Stacks 03LU under the sheaf-of-sets functor**: the comparison
`(f ≫ g)_*F ⟶ g_*(f_*F)` of Stacks 03LU is, on underlying sheaves of sets, the inverse of the
geometric comparison of Stacks 03G2, part (3).

This is the direction in which `AlgebraicGeometry.Space.moduleChartDirectImageParallelArrow` and
`AlgebraicGeometry.Space.chartDirectImageParallelArrow` use the comparison.  It follows from
`AlgebraicGeometry.Space.moduleSheafFunctor_mapIso_modulePushforwardCompIso_app` by `congrArg`,
since the inverse of `CategoryTheory.Functor.mapIso` is the image of the inverse and the inverse
of `CategoryTheory.Iso.app` is the component of the inverse. -/
theorem moduleSheafFunctor_map_modulePushforwardCompIso_inv_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((modulePushforwardCompIso B S hS f g).inv.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  congrArg Iso.inv (moduleSheafFunctor_mapIso_modulePushforwardCompIso_app B S hS f g F)

end AlgebraicGeometry.Space

end
