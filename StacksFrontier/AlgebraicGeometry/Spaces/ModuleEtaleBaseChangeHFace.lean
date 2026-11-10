module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeSetCube
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeUnitSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.CategoryTheory.Adjunction.MatesCubeComponents

/-!
# The h-face of the modules-over-sets cube

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`.
`AlgebraicGeometry.Space.modulePushforwardSquareComparison` is the comparison `i_*f_* ⟶ f'_*g_*`
of the two composite direct images of `𝒪`-modules around it, and
`AlgebraicGeometry.Space.smallEtaleDirectImageCompIso` gives the corresponding comparison for
sheaves of sets on the small étale sites.  This file proves that the forgetful functor
`CategoryTheory.Sheaf.moduleSheafFunctor` carries the first to the second — the **h-face** of the
modules-over-sets cube of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleEtaleBaseChangeSetCube.lean`, the one face that cube
was missing — then applies the cube, and so proves the canonical-map reading of Stacks 03LX and
Stacks 071Z for an étale square.

## Main results

* `AlgebraicGeometry.Space.isIso_moduleEtaleBaseChangeComparison`: **Stacks 03LX for the ordinary
  direct image, read as a statement about the canonical map, for a cartesian square whose bottom
  arrow is étale.**  This is the statement
  `StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardBaseChangeCanonical.lean` records
  as the one underived thing that reading was owed.
* `AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison_etaleSquare`:
  **the same in every degree**, which is Stacks 071Z read the same way.
* `AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale`: the mate itself, before it is
  conjugated into the étale-restriction spelling — the cube's conclusion.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardSquareComparison`: **the
  h-face**, and
  `AlgebraicGeometry.Space.moduleSetSheafFunctor_map_modulePushforwardSquareComparison`, the same
  with the forgetful functor at the spelling the cube is instantiated at.
* `AlgebraicGeometry.Space.modulePushforwardSquareComparison_val_app`: the same on local
  sections, which is how the h-face is proved.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_inv_app_val_app` and
  `AlgebraicGeometry.Space.eqToHom_modulePushforward_app_val_app`: two of its three factors on
  local sections.  The remaining factor is
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, which this
  file imports rather than restates.
* `AlgebraicGeometry.Space.cubeComponents_moduleSheafFunctor`: **the hypothesis of
  `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app` for this cube, at a module** — the
  component form of the cube identity, with the two vertical faces and the two τ-mates
  discharged as identities and the h-face as its content.

## Main definitions

* `AlgebraicGeometry.Space.moduleSetSheafFunctor`: the forgetful functor with its domain pinned
  to `AlgebraicGeometry.Space.Modules`; see the implementation notes.
* `AlgebraicGeometry.Space.moduleSheafTauFace`: the τ-face 2-square.
* `AlgebraicGeometry.Space.moduleSheafVerticalFace` and
  `AlgebraicGeometry.Space.moduleSheafVerticalFace'`: the two vertical faces, which are
  identities.

## Implementation notes

**The h-face is proved on local sections, and that is what makes it affordable.**  Splitting
`Φ.map ((x ≫ y ≫ z).app N)` into its three factors as morphisms of sheaves is out of budget; the
obstruction is not `CategoryTheory.NatTrans.comp_app` — which is `rfl` here and cheap — but the
comparison of two *composites* whose object arguments are written in the two different spellings
of the same sheaf.  The kernel does not compare such a composite structurally; it reduces
`CategoryTheory.CategoryStruct.comp`, which at these sheaf categories unfolds into the concrete
composition applied to the comparison equivalence of Stacks 03G1, and does not finish.  On
sections there is no composition in a sheaf category at all: every step is a function applied to
an element, and every step below is the instantiation of a lemma stated at variable morphisms
(`AlgebraicGeometry.Space.modulesHom_comp_val_app_apply`,
`CategoryTheory.Sheaf.comp_hom_app_apply`), so no kernel check ever has to reduce one.

**The inverse of the composition comparison is obtained from the forward direction** rather than
from `CategoryTheory.Functor.compIsoCongr`'s inverse: the forward statement is affordable and the
inverse one is not, and on sections the inverse is determined by the forward map because both are
isomorphisms.

**The τ-face and the two vertical faces are named definitions at a variable morphism.**  Their
types ascribe a composite of functors to the other of its two spellings, and that ascription is
affordable once, at a variable morphism, and not once per occurrence at the concrete morphisms of
the square below.

**The cube's four module categories are pinned, and that is what makes the final application
affordable.**  `AlgebraicGeometry.Space.Modules B S hS Z.1 Z.2` and
`SheafOfModules (AlgebraicGeometry.Space.structureRingSheaf B S hS Z)` are the same type —
`rfl` identifies them, and cheaply — but they are not the same *term*: the first reaches the
underlying category, its `Category` instance and the topology through
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is a plain definition, so none of the four
implicit arguments of `SheafOfModules` agrees syntactically.  The module-category spelling is
therefore recorded differently in different places, and without the pinning described below the
final application records it differently at 19 of some 330 sites: the general lemma's type variables
take their value from the two adjunctions of Stacks 03LU, whose functors are stated at `Modules`,
while the four forgetful functors carry the other spelling into the same application.
Reconciling those 19 sites is a kernel deterministic timeout (about 50.8 s of kernel time, with
elaboration free).

A type *ascription* does not fix it, because an ascription only checks: the implicit type argument
that an elaborated application records is still the unascribed one.  Two things fix it, and both
are needed.

* `AlgebraicGeometry.Space.moduleSetSheafFunctor` gives the forgetful functor a *declared type*
  at `Modules`.  The kernel reads the spelling off this constant's type instead of deriving it.
* `cubeStage1` supplies the four module *categories* as well as the four functors, so that the
  general lemma's type variables cannot take the spelling of the adjunctions instead.

With both, the hypothesis `AlgebraicGeometry.Space.cubeComponents_moduleSheafFunctor` is stated at
the spelling the cube expects, no site disagrees, and the application checks in 0.4 s instead of
timing out in the kernel.

**Pinning relocates the one unavoidable crossing; it is then taken at a variable morphism.**  The
h-face is proved through the generic sheaf-of-modules API, which speaks `SheafOfModules` of a
variable sheaf of rings, so somewhere the two spellings must still meet.  Doing it at the h-face's
concrete composite is again a kernel timeout, for the reason above: the kernel descends into
`CategoryTheory.CategoryStruct.comp` at these sheaf categories.  `moduleSetSheafFunctor_map` and
`natTrans_app_moduleSetSheafFunctor_obj` take the identification at a *variable* morphism and a
*variable* natural transformation, where the terms are small and it is immediate, and
`moduleSetSheafFunctor_map_modulePushforwardSquareComparison` chains the three steps so that
consecutive ones meet at syntactically identical terms.

## What is not proved here

**Stacks 073K, part (1) is not proved, and nothing here carries that attribute.**  Stacks 073K
asserts base change for `g` merely *flat* (and `f` quasi-compact and quasi-separated).  Everything
above assumes `g` étale, which is strictly stronger, so the results are a *special case* of that
tag and are evidence for nothing about the flat case.  They carry Stacks 03LX and Stacks 071Z
instead, with strings saying so.

Nothing here raises a compiler limit, sets an option or disables a linter.

## References

* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoSquare

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The forgetful functor from `𝒪_Z`-modules to sheaves of sets on the small étale site of
`Z`, with its domain pinned to `AlgebraicGeometry.Space.Modules`.**

`CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)` has domain
`SheafOfModules (structureRingSheaf B S hS Z)`, which is the *other* spelling of
`AlgebraicGeometry.Space.Modules B S hS Z.1 Z.2`: the same type, reached through
`AlgebraicGeometry.Space.smallEtaleRingedSite`, whose projections are not reducible.  A type
*ascription* does not fix that, because an ascription only checks: the implicit type argument
that an elaborated application records is still the unascribed one.  A declaration with the
pinned type does fix it.  The spelling is recorded in this constant's type, the kernel reads it
off instead of deriving it, and the identification of the two spellings is paid once, here. -/
noncomputable abbrev moduleSetSheafFunctor (Z : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤ Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS Z)

section Factors

variable {A M Z : AlgebraicSpaces B S hS}

/-- The comparison of direct images of modules, after its inverse, is the identity: on local
sections, as an equation between the two composites. -/
private theorem modulePushforwardCompIso_inv_hom_comp_val_app (a : A ⟶ M) (b : M ⟶ Z)
    (N : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS (a ≫ b)).obj N).val.obj W) :
    (((modulePushforwardCompIso B S hS a b).inv.app N ≫
          (modulePushforwardCompIso B S hS a b).hom.app N)).val.app W x =
      (CategoryStruct.id ((modulePushforward B S hS (a ≫ b)).obj N)).val.app W x :=
  modulesHom_val_app_congr ((modulePushforwardCompIso B S hS a b).inv_hom_id_app N) W x

/-- The comparison of direct images of modules undoes its own inverse on local sections. -/
private theorem modulePushforwardCompIso_hom_inv_val_app (a : A ⟶ M) (b : M ⟶ Z)
    (N : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS (a ≫ b)).obj N).val.obj W) :
    ((modulePushforwardCompIso B S hS a b).hom.app N).val.app W
        (((modulePushforwardCompIso B S hS a b).inv.app N).val.app W x) = x :=
  (modulesHom_comp_val_app_apply ((modulePushforwardCompIso B S hS a b).inv.app N)
        ((modulePushforwardCompIso B S hS a b).hom.app N) W x).symm.trans
    ((modulePushforwardCompIso_inv_hom_comp_val_app B S hS a b N W x).trans
      (modulesHom_id_val_app_apply W x))

/-- The same for the inverse of the comparison.  Read off from the forward direction by
cancelling the two isomorphisms on sections: the inverse is determined by the forward map, and
the forward maps agree. -/
theorem modulePushforwardCompIso_inv_app_val_app (a : A ⟶ M) (b : M ⟶ Z)
    (N : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS (a ≫ b)).obj N).val.obj W) :
    ((modulePushforwardCompIso B S hS a b).inv.app N).val.app W x =
      ((smallEtaleDirectImageCompIso B S hS a b).inv.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj N)).hom.app W x :=
  (Sheaf.iso_inv_hom_app_apply
        ((smallEtaleDirectImageCompIso B S hS a b).app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj N)) W
        (((modulePushforwardCompIso B S hS a b).inv.app N).val.app W x)).symm.trans
    (congrArg
      (fun y ↦ ((smallEtaleDirectImageCompIso B S hS a b).inv.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj N)).hom.app W y)
      ((modulePushforwardCompIso_hom_app_val_app B S hS a b N W
            (((modulePushforwardCompIso B S hS a b).inv.app N).val.app W x)).symm.trans
        (modulePushforwardCompIso_hom_inv_val_app B S hS a b N W x)))

/-- **The forgetful functor carries the transport of the direct image of modules along an
equality of morphisms to the transport for sheaves of sets**, on local sections. -/
theorem eqToHom_modulePushforward_app_val_app {k k' : A ⟶ Z} (w : k = k')
    (N : Modules.{u, u} B S hS A.1 A.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((modulePushforward B S hS k).obj N).val.obj W) :
    ((eqToHom (congrArg (fun m : A ⟶ Z ↦ modulePushforward B S hS m) w)).app N).val.app W x =
      ((eqToHom (congrArg (fun m : A ⟶ Z ↦ smallEtaleDirectImage B S hS m) w)).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj N)).hom.app W x :=
  Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_eqToHom_modulePushforward_app B S hS w N) W x

end Factors

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The component of a composite of three natural transformations is the composite of the
components. -/
private theorem natTrans_comp_comp_app {C D : Type*} [Category C] [Category D] {F G H K : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ K) (X : C) :
    (α ≫ β ≫ γ).app X = α.app X ≫ β.app X ≫ γ.app X :=
  rfl

/-- The first two factors of the square comparison, on a local section. -/
private theorem squareComparison_val_app_head (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((modulePushforward B S hS i ⋙ modulePushforward B S hS f).obj N).val.obj W) :
    ((eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) w)).app N).val.app W
        (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W x) =
      ((eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w)).app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W
        (((smallEtaleDirectImageCompIso B S hS i f).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W x) :=
  (eqToHom_modulePushforward_app_val_app B S hS w N W
        (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W x)).trans
    (congrArg
      (fun z ↦ ((eqToHom
          (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w)).app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W z)
      (modulePushforwardCompIso_hom_app_val_app B S hS i f N W x))

/-- The square comparison of direct images of modules, written out as its three factors.  This
is its definition, read at the level of natural transformations: nothing is projected, which is
what keeps the two transports inside it from being reduced. -/
private theorem modulePushforwardSquareComparison_eq (w : i ≫ f = f' ≫ g) :
    modulePushforwardSquareComparison B S hS i f' f g w =
      (modulePushforwardCompIso B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) w) ≫
        (modulePushforwardCompIso B S hS f' g).inv :=
  rfl

/-- The square comparison of direct images of modules on a local section, as the three factors
applied in turn. -/
private theorem modulePushforwardSquareComparison_val_app_split (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((modulePushforward B S hS i ⋙ modulePushforward B S hS f).obj N).val.obj W) :
    ((modulePushforwardSquareComparison B S hS i f' f g w).app N).val.app W x =
      ((modulePushforwardCompIso B S hS f' g).inv.app N).val.app W
        (((eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) w)).app N).val.app W
          (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W x)) :=
  (modulesHom_val_app_congr
        ((NatTrans.congr_app (modulePushforwardSquareComparison_eq B S hS i f' f g w) N).trans
          (natTrans_comp_comp_app _ _ _ N)) W x).trans
    ((modulesHom_comp_val_app_apply _ _ W x).trans
      (modulesHom_comp_val_app_apply _ _ W
        (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W x)))

/-- The square comparison of direct images of sheaves of sets on a local section, as the three
factors applied in turn. -/
private theorem smallSetSquareComparison_hom_app_apply (w : i ≫ f = f' ≫ g)
    (P : Sheaf (SmallEtale.topology B S hS X'.1) (Type u))
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((smallEtaleDirectImage B S hS i ⋙ smallEtaleDirectImage B S hS f).obj P).obj.obj W) :
    (((smallEtaleDirectImageCompIso B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv).app P).hom.app W x =
      ((smallEtaleDirectImageCompIso B S hS f' g).inv.app P).hom.app W
        (((eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w)).app P).hom.app W
          (((smallEtaleDirectImageCompIso B S hS i f).hom.app P).hom.app W x)) :=
  (Sheaf.hom_congr_app_apply (natTrans_comp_comp_app _ _ _ P) W x).trans
    ((Sheaf.comp_hom_app_apply _ _ W x).trans
      (Sheaf.comp_hom_app_apply _ _ W
        (((smallEtaleDirectImageCompIso B S hS i f).hom.app P).hom.app W x)))

/-- **The comparison of the two composite direct images around a commutative square is the
corresponding comparison for sheaves of sets, on local sections.** -/
theorem modulePushforwardSquareComparison_val_app (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : ((modulePushforward B S hS i ⋙ modulePushforward B S hS f).obj N).val.obj W) :
    ((modulePushforwardSquareComparison B S hS i f' f g w).app N).val.app W x =
      (((smallEtaleDirectImageCompIso B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W x :=
  ((modulePushforwardSquareComparison_val_app_split B S hS i f' f g w N W x).trans
      ((modulePushforwardCompIso_inv_app_val_app B S hS f' g N W
            (((eqToHom (congrArg (fun k : X' ⟶ Y ↦ modulePushforward B S hS k) w)).app N).val.app
              W (((modulePushforwardCompIso B S hS i f).hom.app N).val.app W x))).trans
        (congrArg
          (fun z ↦ ((smallEtaleDirectImageCompIso B S hS f' g).inv.app
              ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N)).hom.app W z)
          (squareComparison_val_app_head B S hS i f' f g w N W x)))).trans
    (smallSetSquareComparison_hom_app_apply B S hS i f' f g w
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) W x).symm

/-- **The h-face of the modules-over-sets cube.**  The forgetful functor from sheaves of modules
to sheaves of sets carries the comparison of the two composite direct images of modules around a
commutative square to the corresponding comparison for sheaves of sets on the small étale
sites. -/
theorem moduleSheafFunctor_map_modulePushforwardSquareComparison (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardSquareComparison B S hS i f' f g w).app N) =
      ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
          (smallEtaleDirectImageCompIso B S hS f' g).inv).app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).obj N) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_eq_of_val_app.{u, u, u + 1} _ _
    (modulePushforwardSquareComparison_val_app B S hS i f' f g w N)

/-- **The pinned forgetful functor and `CategoryTheory.Sheaf.moduleSheafFunctor` of the
structure sheaf act the same way on a morphism of modules.**  Stated at a *variable* morphism:
the identification of the two spellings of the module category is then between small terms and
applying it costs nothing, whereas carrying it out under the concrete composite of the h-face
below is a kernel timeout. -/
theorem moduleSetSheafFunctor_map (Z : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (moduleSetSheafFunctor B S hS Z).map φ =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map φ :=
  rfl

/-- **The same identification under the component of a natural transformation of functors of
sheaves of sets.**  Stated at a *variable* natural transformation, for the same reason. -/
theorem natTrans_app_moduleSetSheafFunctor_obj {Z W : AlgebraicSpaces B S hS}
    {P Q : Sheaf (SmallEtale.topology B S hS Z.1) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS W.1) (Type u)} (θ : P ⟶ Q)
    (N : Modules.{u, u} B S hS Z.1 Z.2) :
    θ.app ((moduleSetSheafFunctor B S hS Z).obj N) =
      θ.app ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj N) :=
  rfl

/-- **The h-face, with the forgetful functor at the pinned spelling.**  The two identifications
of the spellings are taken from the two variable-level bridges above, so that the three steps of
this chain meet at syntactically identical terms and the kernel never has to carry a spelling
identification underneath a composite in a sheaf category. -/
theorem moduleSetSheafFunctor_map_modulePushforwardSquareComparison (w : i ≫ f = f' ≫ g)
    (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (moduleSetSheafFunctor B S hS Y).map
        ((modulePushforwardSquareComparison B S hS i f' f g w).app N) =
      ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
          (smallEtaleDirectImageCompIso B S hS f' g).inv).app
        ((moduleSetSheafFunctor B S hS X').obj N) :=
  ((moduleSetSheafFunctor_map B S hS Y
          ((modulePushforwardSquareComparison B S hS i f' f g w).app N)).trans
      (moduleSheafFunctor_map_modulePushforwardSquareComparison B S hS i f' f g w N)).trans
    (natTrans_app_moduleSetSheafFunctor_obj B S hS ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
      eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
      (smallEtaleDirectImageCompIso B S hS f' g).inv) N).symm

end Square

/-! ### The cube -/

section Cube

/-! #### The τ-face as a named 2-square

Both the type of the τ-face 2-square and the component form of its mate are stated here at a
*variable* étale morphism.  At the concrete morphisms of the square below, the type ascription
inside `CategoryTheory.TwoSquare.mk` — which is the identification
`AlgebraicGeometry.Space.etaleModulePullback_comp_moduleSheafFunctor` of the two composites of
functors — exceeds the elaborator's budget, while at a variable morphism it is immediate and the
instantiation is first-order. -/

section Tau

variable {U V : AlgebraicSpaces B S hS}

/-- **The τ-face of the modules-over-sets cube**: the comparison of the two horizontal left
adjoints, which is the comparison of Stacks 03LW backwards, whiskered by the forgetful
functor. -/
noncomputable def moduleSheafTauFace (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    TwoSquare (moduleSetSheafFunctor B S hS V)
      (modulePullback B S hS h) (smallEtaleSetRestriction B S hS h hh)
      (moduleSetSheafFunctor B S hS U) :=
  TwoSquare.mk _ _ _ _
    (Functor.whiskerRight (modulePullbackIsoEtaleModulePullback B S hS h hh).inv
      (moduleSetSheafFunctor B S hS U))

/-- The τ-face is invertible: it is the forgetful image of the comparison of Stacks 03LW. -/
theorem isIso_moduleSheafTauFace (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    IsIso (moduleSheafTauFace B S hS h hh) :=
  inferInstanceAs (IsIso (Functor.isoWhiskerRight
    (modulePullbackIsoEtaleModulePullback B S hS h hh).symm
    (moduleSetSheafFunctor B S hS U)).hom)

/-- **The mate of the τ-face is the identity 2-square**, at a module.  This is
`AlgebraicGeometry.Space.mateEquiv_moduleSheafFunctor_modulePullbackIso` read on components. -/
theorem mateEquiv_moduleSheafTauFace_app (h : U ⟶ V) (hh : IsEtale B S hS h.hom)
    (M : Modules.{u, u} B S hS U.1 U.2) :
    (mateEquiv (modulePullbackAdjunction B S hS h)
        (smallEtaleSetRestrictionAdjunction B S hS h hh)
        (moduleSheafTauFace B S hS h hh)).app M =
      CategoryStruct.id ((moduleSetSheafFunctor B S hS V).obj
        ((modulePushforward B S hS h).obj M)) :=
  CategoryTheory.NatTrans.congr_app
    (mateEquiv_moduleSheafFunctor_modulePullbackIso B S hS h hh) M

end Tau

/-! #### The two vertical faces as named 2-cells

The forgetful functor carries the direct image of modules to the direct image of sheaves of sets
on the nose (`AlgebraicGeometry.Space.modulePushforward_comp_moduleSheafFunctor`), so both
vertical faces of the cube are identity 2-cells.  They are named here, at a *variable* morphism,
for the same reason as the τ-face: at the concrete morphisms of the square the type ascription is
the identification of two composites of functors, and the kernel check of it is affordable once,
at a variable morphism, and not once per occurrence. -/

section Vertical

variable {U V : AlgebraicSpaces B S hS}

/-- The vertical face of the cube through the direct image along `h`: the identity 2-cell. -/
noncomputable def moduleSheafVerticalFace (h : U ⟶ V) :
    modulePushforward B S hS h ⋙ (moduleSetSheafFunctor B S hS V) ⟶
      (moduleSetSheafFunctor B S hS U) ⋙ smallEtaleDirectImage B S hS h :=
  CategoryStruct.id _

/-- The same 2-cell, read in the other direction. -/
noncomputable def moduleSheafVerticalFace' (h : U ⟶ V) :
    (moduleSetSheafFunctor B S hS U) ⋙ smallEtaleDirectImage B S hS h ⟶
      modulePushforward B S hS h ⋙ (moduleSetSheafFunctor B S hS V) :=
  CategoryStruct.id _

/-- The vertical face is invertible: it is an identity. -/
theorem isIso_moduleSheafVerticalFace (h : U ⟶ V) :
    IsIso (moduleSheafVerticalFace B S hS h) :=
  inferInstanceAs (IsIso (CategoryStruct.id
    (modulePushforward B S hS h ⋙ (moduleSetSheafFunctor B S hS V))))

/-- The vertical face is invertible, in the other direction. -/
theorem isIso_moduleSheafVerticalFace' (h : U ⟶ V) :
    IsIso (moduleSheafVerticalFace' B S hS h) :=
  inferInstanceAs (IsIso (CategoryStruct.id
    ((moduleSetSheafFunctor B S hS U) ⋙ smallEtaleDirectImage B S hS h)))

/-- The components of the vertical face. -/
theorem moduleSheafVerticalFace_app (h : U ⟶ V) (M : Modules.{u, u} B S hS U.1 U.2) :
    (moduleSheafVerticalFace B S hS h).app M =
      CategoryStruct.id ((modulePushforward B S hS h ⋙
        (moduleSetSheafFunctor B S hS V)).obj M) :=
  rfl

/-- The components of the vertical face, in the other direction. -/
theorem moduleSheafVerticalFace'_app (h : U ⟶ V) (M : Modules.{u, u} B S hS U.1 U.2) :
    (moduleSheafVerticalFace' B S hS h).app M =
      CategoryStruct.id (((moduleSetSheafFunctor B S hS U) ⋙
        smallEtaleDirectImage B S hS h).obj M) :=
  rfl

end Vertical

variable {X Y X' Y' : AlgebraicSpaces B S hS}
  (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The forgetful functor from sheaves of modules on the small étale site of an algebraic space
to sheaves of sets reflects isomorphisms.  This is
`Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map`, read as the
instance the cube asks for. -/
theorem reflectsIsomorphisms_moduleSheafFunctor (Z : AlgebraicSpaces B S hS) :
    Functor.ReflectsIsomorphisms (moduleSetSheafFunctor B S hS Z) :=
  ⟨fun {_ _} φ hφ ↦
    Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
      (R := structureRingSheaf B S hS Z) φ hφ⟩

/-- **The cube hypothesis at a module**, in the component form that
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app` consumes.  The two vertical comparisons are
identities, the two mates of the τ-faces are identities by
`AlgebraicGeometry.Space.mateEquiv_moduleSheafTauFace_app`, and what is left is the h-face. -/
theorem cubeComponents_moduleSheafFunctor (w : i ≫ f = f' ≫ g) (hg : IsEtale B S hS g.hom)
    (hi : IsEtale B S hS i.hom) (N : Modules.{u, u} B S hS X'.1 X'.2) :
    (moduleSheafVerticalFace B S hS f).app ((modulePushforward B S hS i).obj N) ≫
        (smallEtaleDirectImage B S hS f).map
          ((mateEquiv (modulePullbackAdjunction B S hS i)
            (smallEtaleSetRestrictionAdjunction B S hS i hi)
            (moduleSheafTauFace B S hS i hi)).app N) ≫
        (TwoSquare.mk (smallEtaleDirectImage B S hS i) (smallEtaleDirectImage B S hS f')
            (smallEtaleDirectImage B S hS f) (smallEtaleDirectImage B S hS g)
            ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
              eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
              (smallEtaleDirectImageCompIso B S hS f' g).inv)).app
          ((moduleSetSheafFunctor B S hS X').obj N) ≫
        (smallEtaleDirectImage B S hS g).map
          ((moduleSheafVerticalFace' B S hS f').app N) =
      (moduleSetSheafFunctor B S hS Y).map
          ((TwoSquare.mk (modulePushforward B S hS i) (modulePushforward B S hS f')
            (modulePushforward B S hS f) (modulePushforward B S hS g)
            (modulePushforwardSquareComparison B S hS i f' f g w)).app N) ≫
        (mateEquiv (modulePullbackAdjunction B S hS g)
          (smallEtaleSetRestrictionAdjunction B S hS g hg)
          (moduleSheafTauFace B S hS g hg)).app
          ((modulePushforward B S hS f').obj N) := by
  rw [mateEquiv_moduleSheafTauFace_app B S hS i hi N,
    mateEquiv_moduleSheafTauFace_app B S hS g hg ((modulePushforward B S hS f').obj N),
    moduleSheafVerticalFace_app B S hS f ((modulePushforward B S hS i).obj N),
    moduleSheafVerticalFace'_app B S hS f' N]
  change CategoryStruct.id ((modulePushforward B S hS f ⋙
            (moduleSetSheafFunctor B S hS Y)).obj
          ((modulePushforward B S hS i).obj N)) ≫
        (smallEtaleDirectImage B S hS f).map
          (CategoryStruct.id ((smallEtaleDirectImage B S hS i).obj
            ((moduleSetSheafFunctor B S hS X').obj N))) ≫
        ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv).app
          ((moduleSetSheafFunctor B S hS X').obj N) ≫
        (smallEtaleDirectImage B S hS g).map
          (CategoryStruct.id ((smallEtaleDirectImage B S hS f').obj
            ((moduleSetSheafFunctor B S hS X').obj N))) =
      (moduleSetSheafFunctor B S hS Y).map
          ((modulePushforwardSquareComparison B S hS i f' f g w).app N) ≫
        CategoryStruct.id ((moduleSetSheafFunctor B S hS Y).obj
          ((modulePushforward B S hS f' ⋙ modulePushforward B S hS g).obj N))
  exact (Category.id_comp _).trans
    ((congrArg
          (fun m ↦ m ≫ ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
                eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
                (smallEtaleDirectImageCompIso B S hS f' g).inv).app
              ((moduleSetSheafFunctor B S hS X').obj N) ≫
            (smallEtaleDirectImage B S hS g).map
              (CategoryStruct.id ((smallEtaleDirectImage B S hS f').obj
                ((moduleSetSheafFunctor B S hS X').obj N))))
          ((smallEtaleDirectImage B S hS f).map_id _)).trans
      ((Category.id_comp _).trans
        ((congrArg
              (fun m ↦ ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
                    eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
                    (smallEtaleDirectImageCompIso B S hS f' g).inv).app
                  ((moduleSetSheafFunctor B S hS X').obj N) ≫ m)
              ((smallEtaleDirectImage B S hS g).map_id _)).trans
          ((Category.comp_id _).trans
            ((moduleSetSheafFunctor_map_modulePushforwardSquareComparison
                B S hS i f' f g w N).symm.trans (Category.comp_id _).symm)))))

/-! #### The cube, applied in stages

The instantiation of `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app` at these concrete
functors is a single application with ten structural arguments and six side conditions, and the
kernel's budget for one declaration does not cover it.  It is therefore performed in stages, each
a declaration of its own with its own budget and with its type inferred rather than written
out. -/

/-- The cube, with the four corner functors and the four adjunctions supplied.

The four *categories* of the front face are supplied too, pinned to
`AlgebraicGeometry.Space.Modules`.  Without that the general lemma's type variables take their
value from the adjunctions, whose functors are stated at `Modules`, while the four forgetful
functors carry the other spelling of the same type into the same application; the component
hypothesis is then stated at one spelling and expected at the other, and the identification is
what the kernel does not finish. -/
private theorem cubeStage1 (hi : IsEtale B S hS i.hom)
    (hg : IsEtale B S hS g.hom) :
    type_of% (Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app
        (C := Modules.{u, u} B S hS X.1 X.2) (D := Modules.{u, u} B S hS X'.1 X'.2)
        (E := Modules.{u, u} B S hS Y.1 Y.2) (F := Modules.{u, u} B S hS Y'.1 Y'.2)
        (ΦC := moduleSetSheafFunctor B S hS X) (ΦD := moduleSetSheafFunctor B S hS X')
        (ΦE := moduleSetSheafFunctor B S hS Y) (ΦF := moduleSetSheafFunctor B S hS Y')
        (G := modulePushforward B S hS f) (H := modulePushforward B S hS f')
        (G' := smallEtaleDirectImage B S hS f) (H' := smallEtaleDirectImage B S hS f')
        (modulePullbackAdjunction B S hS i) (modulePullbackAdjunction B S hS g)
        (smallEtaleSetRestrictionAdjunction B S hS i hi)
        (smallEtaleSetRestrictionAdjunction B S hS g hg)) :=
  Stacks.CategoryTheory.isIso_mateEquiv_symm_of_app
    (C := Modules.{u, u} B S hS X.1 X.2) (D := Modules.{u, u} B S hS X'.1 X'.2)
    (E := Modules.{u, u} B S hS Y.1 Y.2) (F := Modules.{u, u} B S hS Y'.1 Y'.2)
    (ΦC := moduleSetSheafFunctor B S hS X) (ΦD := moduleSetSheafFunctor B S hS X')
    (ΦE := moduleSetSheafFunctor B S hS Y) (ΦF := moduleSetSheafFunctor B S hS Y')
    (G := modulePushforward B S hS f) (H := modulePushforward B S hS f')
    (G' := smallEtaleDirectImage B S hS f) (H' := smallEtaleDirectImage B S hS f')
    (modulePullbackAdjunction B S hS i) (modulePullbackAdjunction B S hS g)
    (smallEtaleSetRestrictionAdjunction B S hS i hi)
    (smallEtaleSetRestrictionAdjunction B S hS g hg)

/-- The cube, with the τ-faces and the vertical faces supplied. -/
private theorem cubeStage2 (hi : IsEtale B S hS i.hom)
    (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage1 B S hS i f' f g hi hg (moduleSheafTauFace B S hS i hi)
        (moduleSheafTauFace B S hS g hg) (moduleSheafVerticalFace B S hS f)
        (moduleSheafVerticalFace' B S hS f')) :=
  cubeStage1 B S hS i f' f g hi hg (moduleSheafTauFace B S hS i hi)
    (moduleSheafTauFace B S hS g hg) (moduleSheafVerticalFace B S hS f)
    (moduleSheafVerticalFace' B S hS f')

/-- The cube, with the two 2-cells supplied. -/
private theorem cubeStage3 (w : i ≫ f = f' ≫ g)
    (hi : IsEtale B S hS i.hom) (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage2 B S hS i f' f g hi hg
        (TwoSquare.mk (modulePushforward B S hS i) (modulePushforward B S hS f')
          (modulePushforward B S hS f) (modulePushforward B S hS g)
          (modulePushforwardSquareComparison B S hS i f' f g w))
        (TwoSquare.mk (smallEtaleDirectImage B S hS i) (smallEtaleDirectImage B S hS f')
          (smallEtaleDirectImage B S hS f) (smallEtaleDirectImage B S hS g)
          ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
            eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
            (smallEtaleDirectImageCompIso B S hS f' g).inv))) :=
  cubeStage2 B S hS i f' f g hi hg
    (TwoSquare.mk (modulePushforward B S hS i) (modulePushforward B S hS f')
      (modulePushforward B S hS f) (modulePushforward B S hS g)
      (modulePushforwardSquareComparison B S hS i f' f g w))
    (TwoSquare.mk (smallEtaleDirectImage B S hS i) (smallEtaleDirectImage B S hS f')
      (smallEtaleDirectImage B S hS f) (smallEtaleDirectImage B S hS g)
      ((smallEtaleDirectImageCompIso B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y ↦ smallEtaleDirectImage B S hS k) w) ≫
        (smallEtaleDirectImageCompIso B S hS f' g).inv))

/-- The cube, with the reflection of isomorphisms and the invertibility of the τ-faces
supplied. -/
private theorem cubeStage4 (w : i ≫ f = f' ≫ g)
    (hi : IsEtale B S hS i.hom) (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage3 B S hS i f' f g w hi hg (reflectsIsomorphisms_moduleSheafFunctor B S hS Y')
        (isIso_moduleSheafTauFace B S hS i hi) (isIso_moduleSheafTauFace B S hS g hg)) :=
  cubeStage3 B S hS i f' f g w hi hg (reflectsIsomorphisms_moduleSheafFunctor B S hS Y')
    (isIso_moduleSheafTauFace B S hS i hi) (isIso_moduleSheafTauFace B S hS g hg)

/-- The cube, with the invertibility of the vertical faces supplied. -/
private theorem cubeStage5 (w : i ≫ f = f' ≫ g)
    (hi : IsEtale B S hS i.hom) (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage4 B S hS i f' f g w hi hg (isIso_moduleSheafVerticalFace B S hS f)
        (isIso_moduleSheafVerticalFace' B S hS f')) :=
  cubeStage4 B S hS i f' f g w hi hg (isIso_moduleSheafVerticalFace B S hS f)
    (isIso_moduleSheafVerticalFace' B S hS f')

/-- The cube, with the back face supplied: Stacks 03LR, part (1) for the canonical map on the
small étale sites at `Type u`. -/
private theorem cubeStage6 (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage5 B S hS i f' f g sq.w (isEtale_of_isPullback B S hS f' i g f sq.flip hg) hg
        (isIso_mateEquiv_symm_smallSetPushforwardCompSquare B S hS i f' f g sq hg)) :=
  cubeStage5 B S hS i f' f g sq.w (isEtale_of_isPullback B S hS f' i g f sq.flip hg) hg
    (isIso_mateEquiv_symm_smallSetPushforwardCompSquare B S hS i f' f g sq hg)

/-- The cube, with the component hypothesis supplied: the application that the pinning of the
four module categories makes affordable.  Its type is inferred, as the stages' are. -/
private theorem cubeStage7 (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    type_of% (cubeStage6 B S hS i f' f g sq hg
        (cubeComponents_moduleSheafFunctor B S hS i f' f g sq.w hg
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))) :=
  cubeStage6 B S hS i f' f g sq hg
    (cubeComponents_moduleSheafFunctor B S hS i f' f g sq.w hg
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))

/-- **The base-change map of an étale square is an isomorphism.**  For a cartesian square of
algebraic spaces whose bottom arrow `g` is étale, the base change map
`g^*f_* ⟶ f'_*(i^*-)` of `AlgebraicGeometry.Space.moduleBaseChangeMap` — the mate, across the
two adjunctions of Stacks 03LU, of the comparison of the two composite direct images around the
square — is invertible.

This is the modules-over-sets cube: the forgetful functor to sheaves of sets on the small étale
site reflects isomorphisms, it carries the direct image of modules to the direct image of sheaves
of sets and the étale inverse image to restriction on the nose, so the two vertical comparisons
of the cube are identities and the two τ-mates are identities; the h-face is
`AlgebraicGeometry.Space.moduleSetSheafFunctor_map_modulePushforwardSquareComparison`, and the
back face is
`AlgebraicGeometry.Space.isIso_mateEquiv_symm_smallSetPushforwardCompSquare`, which is Stacks
03LR, part (1) for the canonical map on the small étale sites at `Type u`.

Étale, not flat: `hg` is `AlgebraicGeometry.Space.IsEtale`.  So this is **not** Stacks 073K,
part (1), which asserts the same for `g` merely flat and `f` quasi-compact and quasi-separated;
étale is strictly stronger than flat, and nothing here is evidence for the flat case. -/
theorem isIso_moduleBaseChangeMap_of_isEtale (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) : IsIso (moduleBaseChangeMap f g f' i sq.w) :=
  cubeStage7 B S hS i f' f g sq hg

/-! ### Stacks 03LX and Stacks 071Z for the canonical maps of an étale square -/

/-- **Stacks 03LX for the ordinary direct image, read as a statement about the canonical map, in
the étale case.**  For a cartesian square of algebraic spaces whose bottom arrow `g` is étale,
the canonical base-change comparison

`(f_*F)|_{Y'} ⟶ f'_*(F|_{X'})`

of `AlgebraicGeometry.Space.moduleEtaleBaseChangeComparison` is an isomorphism.

This is what
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardBaseChangeCanonical.lean` records as
the single underived statement the canonical reading of Stacks 03LX and Stacks 071Z was owed.  It is
`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale` conjugated into the étale-restriction
spelling by Stacks 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is
canonical, so the conjugation introduces no twist.

**This is the étale case and not Stacks 073K, part (1).**  Stacks 073K, part (1) asserts base
change for `g` merely *flat* and `f` quasi-compact and quasi-separated; `hg` here is
`AlgebraicGeometry.Space.IsEtale`, and étale is strictly stronger than flat.  So this is a
special case of that tag and carries no attribute for it. -/
@[stacks 03LX "the ordinary direct image, for the CANONICAL comparison map and for an ÉTALE
square: g étale, not merely flat, so this is a special case of Stacks 073K part (1) and not
that tag.  The existing 03LX attributes carry isomorphisms with the right endpoints that are
not identified with the canonical map"]
theorem isIso_moduleEtaleBaseChangeComparison (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (moduleEtaleBaseChangeComparison B S hS i f' f g sq hg) := by
  have hβ := isIso_moduleBaseChangeMap_of_isEtale B S hS i f' f g sq hg
  have hl : IsIso (Functor.whiskerLeft (modulePushforward B S hS f)
      (modulePullbackIsoEtaleModulePullback B S hS g hg).inv) :=
    inferInstanceAs (IsIso (Functor.isoWhiskerLeft (modulePushforward B S hS f)
      (modulePullbackIsoEtaleModulePullback B S hS g hg)).inv)
  have hr : IsIso (Functor.whiskerRight
      (modulePullbackIsoEtaleModulePullback B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).hom
      (modulePushforward B S hS f')) :=
    inferInstanceAs (IsIso (Functor.isoWhiskerRight
      (modulePullbackIsoEtaleModulePullback B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (modulePushforward B S hS f')).hom)
  exact inferInstanceAs (IsIso (_ ≫ _ ≫ _))

/-! #### Every positive degree

`AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison` derives the
canonical comparison in every degree from the underived one by canonical steps alone, so with
the statement above its hypothesis is discharged and nothing in positive degree is owed.

The two `local` priority raises are the ones
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardBaseChangeCanonical.lean` explains:
two global instances stated at module universe `max u v r w` capture instance search for
`Abelian` and `EnoughInjectives` at module universe `u` and then fail on the universe
constraint. -/

section HigherDegree

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **Stacks 071Z read as a statement about the canonical maps, in the étale case.**  For a
cartesian square of algebraic spaces whose bottom arrow `g` is étale, the canonical base-change
comparison

`(R^n f_*F)|_{Y'} ⟶ R^n f'_*(F|_{X'})`

is an isomorphism in every degree `n`.

This is `AlgebraicGeometry.Space.isIso_moduleHigherPushforwardEtaleBaseChangeComparison` with its
underived hypothesis discharged by
`AlgebraicGeometry.Space.isIso_moduleEtaleBaseChangeComparison`.  The injective-preservation
input of the comparison map — part (1) of Stacks 03F3 for étale restriction of modules along `i`,
which is étale by Stacks 03FU — is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` and is used, not assumed.
So nothing is assumed here beyond the cartesian square and the étaleness of `g`.

**This is the étale case and not Stacks 073K, part (1)**, for the same reason as the underived
statement: `hg` is `AlgebraicGeometry.Space.IsEtale`, and étale is strictly stronger than the
flatness of `g` that Stacks 073K assumes. -/
@[stacks 071Z "for the CANONICAL comparison map and for an ÉTALE square: g étale, not merely
flat, so this is a special case of Stacks 073K part (1) and not that tag.  The existing 071Z
attribute carries an isomorphism with the right endpoints that is not identified with the
canonical map"]
theorem isIso_moduleHigherPushforwardEtaleBaseChangeComparison_etaleSquare
    (sq : IsPullback i f' f g) (hg : IsEtale B S hS g.hom) (n : ℕ) :
    IsIso (moduleHigherPushforwardEtaleBaseChangeComparison B S hS i f' f g sq hg
      (preservesInjectiveObjects_etaleModulePullback B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)) n) :=
  isIso_moduleHigherPushforwardEtaleBaseChangeComparison B S hS i f' f g sq hg
    (preservesInjectiveObjects_etaleModulePullback B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
    (isIso_moduleEtaleBaseChangeComparison B S hS i f' f g sq hg) n

end HigherDegree

end Cube

end AlgebraicGeometry.Space

end
