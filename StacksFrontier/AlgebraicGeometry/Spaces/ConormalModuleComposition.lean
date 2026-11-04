module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart

/-!
# The composition law for the map of defining ideal sheaves of a commutative square

Let there be two vertically composable commutative squares of closed subspaces of algebraic
spaces over a scheme `S` contained in a big fppf site `B`: closed subspaces `Z ⊆ X`, `Z' ⊆ X'`,
`Z'' ⊆ X''`, morphisms `g : X ⟶ X'`, `g' : X' ⟶ X''` of the ambient spaces and `f : Z ⟶ Z'`,
`f' : Z' ⟶ Z''` of the subspaces, with both squares of inclusions commuting.  This file proves
that the maps `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves of [Stacks Project, Tag 04CP] compose: the
map of the outer rectangle is the inverse image along `g` of the map of the lower square followed
by the map of the upper square, read through the composition comparison of [Stacks Project,
Tag 03LU].

The proof is the one the source indicates.  Both sides are morphisms into the defining ideal
sheaf `𝓘` of `Z`, whose inclusion `𝓘 ⊆ 𝒪_X` is a monomorphism, so it suffices to compare them
after that inclusion; and
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` turns each of the three maps of
ideal sheaves into the inverse image of an inclusion followed by the canonical comparison
`g^*𝒪_{X'} ⟶ 𝒪_X`.  What is left is the composition law for that comparison, which is the main
work of this file.

## Main results

* `AlgebraicGeometry.Space.structureModulePullbackMap_comp`: **the canonical comparison
  `g^*𝒪_{X'} ⟶ 𝒪_X` composes.**  For `g : X ⟶ X'` and `g' : X' ⟶ X''` the comparison of the
  composite is the composition comparison of [Stacks Project, Tag 03LU], followed by the inverse
  image along `g` of the comparison of `g'`, followed by the comparison of `g`.
* `AlgebraicGeometry.Space.idealSheafMap_comp`: **the composition law for the map of defining
  ideal sheaves**, part (3) of [Stacks Project, Tag 04G2] at the level of ideal sheaves.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_homEquiv_structureModulePullbackMap`: the
  transpose of the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is, on underlying sheaves of sets, the structure
  map `g^♯ : 𝒪_{X'} ⟶ g_*𝒪_X` of [Stacks Project, Tag 03G8].
* `AlgebraicGeometry.Space.isIso_conormalMap_comp_iff`: **the conormal map of a composite is
  invertible exactly when the composite of the two conormal maps is**, part (3) of [Stacks
  Project, Tag 04G2] in the form invertibility consumes, with no hypothesis on either side.
* `AlgebraicGeometry.Space.isIso_comp_conormalMap_of_isIso_conormalMap`: **invertibility of the
  conormal map of a composite descends to the two factors**, part (3) of [Stacks Project,
  Tag 04G2] in the form invertibility consumes.
* `AlgebraicGeometry.Space.conormalMap_comp`: **the composition formula for conormal maps**,
  part (3) of [Stacks Project, Tag 04G2]: the conormal map of the outer rectangle is the inverse
  image of the conormal map of the lower square followed by that of the upper square.
* `AlgebraicGeometry.Space.conormalMap_comp_of_eq`: the same formula with the upper edge of the
  outer rectangle and the composition comparison of [Stacks Project, Tag 03LU] handed over in
  arguments, so that a consumer whose goal spells that edge otherwise than `f ≫ f'` supplies the
  identification in an argument rather than asking for it under a `CategoryTheory.Functor.map`;
  see the implementation notes for what that buys and what it does not.
* `AlgebraicGeometry.Space.conormalMap_comp_triangle`: the same formula with the upper edge of
  the outer rectangle a variable and the comparison of [Stacks Project, Tag 03LU] read off that
  variable's defining equation through `AlgebraicGeometry.Space.modulePullbackTriangle`, so that
  the consumer supplies no identification at all; this is the form in which the restriction
  stability of condition (3) of [Stacks Project, Tag 061A] consumes the law.
* `AlgebraicGeometry.Space.conormalMap_comp_triangle_of_eq`: the same formula with that
  comparison abstracted into a variable natural transformation whose value is given by a separate
  equation, so that it is strictly more general than the previous one.  It does *not*
  make any instance of the law cheaper, and its docstring explains why.
* `AlgebraicGeometry.Space.conormalMap_comp_triangle_of_spaces`: the same formula with the
  ambient algebraic spaces of the three closed subspaces, the three edges, the three conormal
  modules and the three conormal maps all carried as variables whose values are given by
  equations of spaces and heterogeneous equalities, so that a consumer spelling those ambient
  spaces otherwise meets the law only at a `Quiver.Hom` of
  `AlgebraicGeometry.Space.Modules`.  This is the form in which the restriction stability of
  condition (3) of [Stacks Project, Tag 061A] consumes the law; its docstring records what it
  buys and how it differs from `AlgebraicGeometry.Space.conormalMap_comp_of_spaces`.

## Implementation notes

The composition law for the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is proved by transposing along the
adjunction of [Stacks Project, Tag 03D7], where the composition comparison of inverse images
becomes the one of direct images
(`AlgebraicGeometry.Space.homEquiv_modulePullbackCompIso_inv_app_comp`), and then by identifying
the transposed comparison with the structure map of [Stacks Project, Tag 03G8] on underlying
sheaves of sets.  That identification is chartwise: the chart projections of the transpose are
the components of `AlgebraicGeometry.Space.structureModuleFMap`, which are pullback of regular
functions along the vertical morphism of a chart diagram, and
`AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp` says the same of the structure
map.  The composition law for the structure map on underlying sheaves of sets is
`AlgebraicGeometry.Space.structureSharpSet_comp`, and the composition comparison of direct images
of modules is the geometric comparison of [Stacks Project, Tag 03G2], part (3), on underlying
sheaves of sets by `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`.

Two spellings of the same sheaf of sets occur throughout — the underlying sheaf of a direct image
of modules, and the direct image of the underlying sheaf — and they are reconciled only by
unfolding semireducible definitions.  Every step below that crosses between them is therefore
taken on *sections*, where the identification is between two types rather than between two
sheaves of types; this is the discipline recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsComp.lean`, and it is why the auxiliary
statements below are stated on sections.

For the composition law for the conormal map both composites are factored through the inverse
image along the inclusion of `Z` of the two maps of defining ideal sheaves, which is the factor
they share; the two remaining left factors are composites of comparison isomorphisms, so
invertibility passes from the outer rectangle to the shared factor and from there to the
composite of the two squares.  Those statements compare `(g'^* ⋙ g^*)𝓘''` with `g^*(g'^*𝓘'')`,
and the inverse image is made locally irreducible there: the two agree by the definition of a
composite of functors, while unfolding the inverse image to its construction by sheafification
does not terminate.

**Why `AlgebraicGeometry.Space.conormalMap_comp_of_eq` exists.**  The composition law
quantifies over the upper edge `f'`, so a consumer may instantiate it at a composite; what a
consumer cannot afford is to *write down* the resulting statement.  With the law restated by hand
at `f' := p ≫ a` — every closed subspace, every projection and every horizontal morphism still a
variable — deciding that hand-written statement against the instance exhausts the default budget,
and so does specialising a version proved over an abstract `pa` to `pa := p ≫ a`; both are free
while `f'` is a variable.  The variant above removes the need to write it: the upper edge of the
outer rectangle is a variable with its value in an equation, and the comparison of
[Stacks Project, Tag 03LU] is a variable with its value in a heterogeneous equality, so a
consumer whose own edge is `(q ≫ p) ≫ a` supplies `CategoryTheory.Category.assoc` and `HEq.rfl`
and the two bracketings never meet under a `CategoryTheory.Functor.map`.  Both discharges are
crossings at `CategoryTheory.Functor.obj`, which is a congruence here, rather than at
`CategoryTheory.Functor.map` or `CategoryTheory.NatTrans.app`, which reduce their projection
first.

What it does *not* buy is the whole of the restriction stability of condition (3) of
[Stacks Project, Tag 061A]; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftSheaf.lean` record where the remaining cost
is, and that it is no longer in this law.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS} (g : X ⟶ X') (g' : X' ⟶ X'')

/-- Equal morphisms of modules on the small étale site of an algebraic space agree on every
local section. -/
private theorem val_app_congr {W : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS W.1 W.2} {x y : M ⟶ N} (h : x = y)
    (U : (SmallEtale B S hS W.1)ᵒᵖ) (s : M.val.obj U) :
    x.val.app U s = y.val.app U s :=
  congrArg (fun m : M ⟶ N ↦ m.val.app U s) h

/-- Evaluating a composite of morphisms of modules on a local section is evaluating the two
factors in turn. -/
private theorem comp_val_app {W : AlgebraicSpaces B S hS}
    {M N P : Modules.{u, u} B S hS W.1 W.2} (a : M ⟶ N) (b : N ⟶ P)
    (U : (SmallEtale B S hS W.1)ᵒᵖ) (s : M.val.obj U) :
    (a ≫ b).val.app U s = b.val.app U (a.val.app U s) :=
  rfl

/-! ### The transpose of the comparison of structure sheaves is the structure map -/

/-- A chart projection of the transpose of the canonical comparison `g^*𝒪_{X'} ⟶ 𝒪_X` agrees
with the corresponding chart projection of the structure map `g^♯` of [Stacks Project,
Tag 03G8]: both are pullback of regular functions along the morphism of charts. -/
private theorem moduleChartProjection_app_homEquiv_structureModulePullbackMap
    (V : SmallEtale B S hS X'.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g V)) (comparisonFunctor B S hS X).op)
    (r : (structureSetSheaf B S hS X').obj.obj (op V)) :
    (moduleChartProjection B S hS g V j).app (structureSetSheaf B S hS X)
        (((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g)).val.app (op V) r) =
      (moduleChartProjection B S hS g V j).app (structureSetSheaf B S hS X)
        ((structureSharpSet B S hS g).hom.app (op V) r) := by
  rw [structureModulePullbackMap_transpose B S hS g]
  refine Eq.trans (moduleChartProjection_app_moduleFMapSection B S hS g
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
    (structureModuleFMap B S hS g) V j r) ?_
  refine Eq.trans ?_ (moduleChartProjection_app_structureSharp B S hS g V j r).symm
  rfl

/-- On the sections over an étale scheme chart, the transpose of the canonical comparison
`g^*𝒪_{X'} ⟶ 𝒪_X` along the adjunction of [Stacks Project, Tag 03D7] is the structure map
`g^♯ : 𝒪_{X'} ⟶ g_*𝒪_X` of [Stacks Project, Tag 03G8]: a section of a direct image is determined
by its chart projections. -/
private theorem homEquiv_structureModulePullbackMap_val_app_chart
    (V : SmallEtale B S hS X'.1) (r : (structureSetSheaf B S hS X').obj.obj (op V)) :
    ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g)).val.app (op V) r =
      (structureSharpSet B S hS g).hom.app (op V) r :=
  moduleChartProjection_ext B S hS g V (structureSetSheaf B S hS X)
    (moduleChartProjection_app_homEquiv_structureModulePullbackMap B S hS g V · r)

/-- `AlgebraicGeometry.Space.homEquiv_structureModulePullbackMap_val_app_chart` with the chart
written as an object of the opposite category. -/
private theorem homEquiv_structureModulePullbackMap_val_app
    (W : (SmallEtale B S hS X'.1)ᵒᵖ) (r : (structureSetSheaf B S hS X').obj.obj W) :
    ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g)).val.app W r =
      (structureSharpSet B S hS g).hom.app W r :=
  homEquiv_structureModulePullbackMap_val_app_chart B S hS g W.unop r

/-- **The transpose of the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is the structure map of
[Stacks Project, Tag 03G8].**  The transpose along the adjunction of [Stacks Project, Tag 03D7]
of `AlgebraicGeometry.Space.structureModulePullbackMap` is, on underlying sheaves of sets, the
structure map `g^♯ : 𝒪_{X'} ⟶ g_*𝒪_X`. -/
theorem moduleSheafFunctor_map_homEquiv_structureModulePullbackMap :
    (show structureSetSheaf B S hS X' ⟶
        (smallEtaleDirectImage B S hS g).obj (structureSetSheaf B S hS X) from
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g))) =
      structureSharpSet B S hS g := by
  refine Sheaf.hom_ext (CategoryTheory.NatTrans.ext (funext fun W ↦
    ConcreteCategory.hom_ext _ _ fun r ↦ ?_))
  exact homEquiv_structureModulePullbackMap_val_app B S hS g W r

/-- The direct image along `g'` of the transpose of the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is, on
underlying sheaves of sets, the direct image along `g'` of the structure map `g^♯`. -/
private theorem moduleSheafFunctor_map_modulePushforward_map_homEquiv :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X'')).map
        ((modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g))) =
      (smallEtaleDirectImage B S hS g').map (structureSharpSet B S hS g) :=
  (moduleSheafFunctor_map_modulePushforward_map B S hS g' _).trans
    (congrArg (smallEtaleDirectImage B S hS g').map
      (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS g))

/-- The previous identification, read on a local section. -/
private theorem modulePushforward_map_homEquiv_val_app
    (W : (SmallEtale B S hS X''.1)ᵒᵖ)
    (x : ((modulePushforward B S hS g').obj
      (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.obj W) :
    ((modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g))).val.app W x =
      ((smallEtaleDirectImage B S hS g').map (structureSharpSet B S hS g)).hom.app W x :=
  Sheaf.hom_congr_app_apply
    (moduleSheafFunctor_map_modulePushforward_map_homEquiv B S hS g g') W x

/-- The composition comparison of direct images of [Stacks Project, Tag 03LU] at the structure
sheaf, in its transported form, is the geometric comparison of [Stacks Project, Tag 03G2],
part (3), on underlying sheaves of sets. -/
private theorem moduleSheafFunctor_map_compIsoCongr_hom_app_unit :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X'')).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS g')
          (pushforwardModules_eq_modulePushforward B S hS (g ≫ g'))
          (pushforwardModulesCompAt B S hS g g')).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS X))) =
      (smallToposMorphismTypeU_comp B S hS g g').hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X))) :=
  moduleSheafFunctor_map_compIsoCongr_hom_app B S hS g g'
    (SheafOfModules.unit (structureRingSheaf B S hS X))

/-- On a local section, the composition comparison of direct images of [Stacks Project,
Tag 03LU] at the structure sheaf is the geometric comparison of [Stacks Project, Tag 03G2],
part (3). -/
private theorem modulePushforwardCompIso_hom_app_unit_val_app
    (W : (SmallEtale B S hS X''.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g').obj ((modulePushforward B S hS g).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))).val.obj W) :
    ((modulePushforwardCompIso B S hS g g').hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app W z =
      ((smallToposMorphismTypeU_comp B S hS g g').hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X)))).hom.app W z :=
  (val_app_congr B S hS (modulePushforwardCompIso_hom_app_eq B S hS g g'
      (SheafOfModules.unit (structureRingSheaf B S hS X))) W z).trans
    (Sheaf.hom_congr_app_apply
      (moduleSheafFunctor_map_compIsoCongr_hom_app_unit B S hS g g') W z)

/-! ### The composition law for the comparison of structure sheaves -/

/-- The transposed form of `AlgebraicGeometry.Space.structureModulePullbackMap_comp`: the
transpose of the comparison of a composite is the transpose for `g'`, the direct image along `g'`
of the transpose for `g`, and the composition comparison of direct images.  This is the
composition law `AlgebraicGeometry.Space.structureSharpSet_comp` for the structure map of
[Stacks Project, Tag 03G8], read through the identification of the transpose with it. -/
private theorem homEquiv_structureModulePullbackMap_comp_val_app
    (W : (SmallEtale B S hS X''.1)ᵒᵖ)
    (r : (SheafOfModules.unit (structureRingSheaf B S hS X'')).val.obj W) :
    ((modulePullbackAdjunction B S hS (g ≫ g')).homEquiv _ _
        (structureModulePullbackMap B S hS (g ≫ g'))).val.app W r =
      ((modulePushforwardCompIso B S hS g g').hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app W
        (((modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g))).val.app W
            (((modulePullbackAdjunction B S hS g').homEquiv _ _
              (structureModulePullbackMap B S hS g')).val.app W r)) := by
  refine Eq.trans (homEquiv_structureModulePullbackMap_val_app B S hS (g ≫ g') W r) ?_
  refine Eq.trans (Sheaf.hom_congr_app_apply
    (structureSharpSet_comp B S hS g g') W r).symm ?_
  refine Eq.trans (congrArg (((smallToposMorphismTypeU_comp B S hS g g').hom.app
      (structureSetSheaf B S hS X)).hom.app W)
    (congrArg (((smallEtaleDirectImage B S hS g').map
      (structureSharpSet B S hS g)).hom.app W)
        (homEquiv_structureModulePullbackMap_val_app B S hS g' W r).symm)) ?_
  refine Eq.trans (congrArg (((smallToposMorphismTypeU_comp B S hS g g').hom.app
      (structureSetSheaf B S hS X)).hom.app W)
    (modulePushforward_map_homEquiv_val_app B S hS g g' W
      (((modulePullbackAdjunction B S hS g').homEquiv _ _
        (structureModulePullbackMap B S hS g')).val.app W r)).symm) ?_
  exact (modulePushforwardCompIso_hom_app_unit_val_app B S hS g g' W
    (((modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
      (structureModulePullbackMap B S hS g))).val.app W
        (((modulePullbackAdjunction B S hS g').homEquiv _ _
          (structureModulePullbackMap B S hS g')).val.app W r))).symm

/-- The transposed form of `AlgebraicGeometry.Space.structureModulePullbackMap_comp`: the
transpose of the comparison of a composite is the transpose for `g'`, the direct image along `g'`
of the transpose for `g`, and the composition comparison of direct images. -/
private theorem homEquiv_structureModulePullbackMap_comp :
    (modulePullbackAdjunction B S hS (g ≫ g')).homEquiv _ _
        (structureModulePullbackMap B S hS (g ≫ g')) =
      ((modulePullbackAdjunction B S hS g').homEquiv _ _
          (structureModulePullbackMap B S hS g') ≫
        (modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g))) ≫
      (modulePushforwardCompIso B S hS g g').hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦
    ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_))
  refine Eq.trans (homEquiv_structureModulePullbackMap_comp_val_app B S hS g g' W r) ?_
  refine Eq.trans ?_ (comp_val_app B S hS
    ((modulePullbackAdjunction B S hS g').homEquiv _ _
        (structureModulePullbackMap B S hS g') ≫
      (modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g)))
    ((modulePushforwardCompIso B S hS g g').hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X))) W r).symm
  exact congrArg (((modulePushforwardCompIso B S hS g g').hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app W)
    (comp_val_app B S hS
      ((modulePullbackAdjunction B S hS g').homEquiv _ _
        (structureModulePullbackMap B S hS g'))
      ((modulePushforward B S hS g').map ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureModulePullbackMap B S hS g))) W r).symm

/-- **The canonical comparison `g^*𝒪_{X'} ⟶ 𝒪_X` composes.**  For `g : X ⟶ X'` and
`g' : X' ⟶ X''` the comparison of the composite is the composition comparison of inverse images
of [Stacks Project, Tag 03LU], followed by the inverse image along `g` of the comparison of `g'`,
followed by the comparison of `g`. -/
theorem structureModulePullbackMap_comp :
    structureModulePullbackMap B S hS (g ≫ g') =
      (modulePullbackCompIso B S hS g g').inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'')) ≫
        (modulePullback B S hS g).map (structureModulePullbackMap B S hS g') ≫
        structureModulePullbackMap B S hS g := by
  have h1 : (modulePullbackAdjunction B S hS g).homEquiv _ _
        ((modulePullback B S hS g).map (structureModulePullbackMap B S hS g') ≫
          structureModulePullbackMap B S hS g) =
      structureModulePullbackMap B S hS g' ≫
        (modulePullbackAdjunction B S hS g).homEquiv _ _
          (structureModulePullbackMap B S hS g) :=
    Adjunction.homEquiv_naturality_left _ _ _
  have h2 : (modulePullbackAdjunction B S hS g').homEquiv _ _
        (structureModulePullbackMap B S hS g' ≫
          (modulePullbackAdjunction B S hS g).homEquiv _ _
            (structureModulePullbackMap B S hS g)) =
      (modulePullbackAdjunction B S hS g').homEquiv _ _
          (structureModulePullbackMap B S hS g') ≫
        (modulePushforward B S hS g').map
          ((modulePullbackAdjunction B S hS g).homEquiv _ _
            (structureModulePullbackMap B S hS g)) :=
    Adjunction.homEquiv_naturality_right _ _ _
  have h3 := (congrArg ((modulePullbackAdjunction B S hS g').homEquiv
    (SheafOfModules.unit (structureRingSheaf B S hS X''))
    ((modulePushforward B S hS g).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)))) h1).trans h2
  refine ((modulePullbackAdjunction B S hS (g ≫ g')).homEquiv _ _).injective ?_
  refine Eq.trans ?_ (homEquiv_modulePullbackCompIso_inv_app_comp B S hS g g'
    (SheafOfModules.unit (structureRingSheaf B S hS X''))
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    ((modulePullback B S hS g).map (structureModulePullbackMap B S hS g') ≫
      structureModulePullbackMap B S hS g)).symm
  rw [h3]
  exact homEquiv_structureModulePullbackMap_comp B S hS g g'

/-! ### The composition law for the map of defining ideal sheaves -/

/-- **The composition law for the map of defining ideal sheaves**, part (3) of [Stacks Project,
Tag 04G2] at the level of ideal sheaves.  For two vertically composable commutative squares of
closed subspaces, the map `(g ≫ g')^*𝓘'' ⟶ 𝓘` of [Stacks Project, Tag 04CP] attached to the
outer rectangle is the composition comparison of [Stacks Project, Tag 03LU], followed by the
inverse image along `g` of the map of the lower square, followed by the map of the upper
square. -/
theorem idealSheafMap_comp (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'') :
    idealSheafMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' =
      (modulePullbackCompIso B S hS g g').inv.app
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules ≫
        (modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq') ≫
          idealSheafMap B S hS Z Z' g f hsq := by
  refine (cancel_mono (definingIdealSheaf B S hS X Z).ι).mp ?_
  have hCC : (modulePullbackCompIso B S hS g g').inv.app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules =
      (modulePullbackCompIso B S hS g g').inv.app
        (definingIdealSheaf B S hS X'' Z'').toSheafOfModules :=
    rfl
  have hnat := (modulePullbackCompIso B S hS g g').inv.naturality
    (definingIdealSheaf B S hS X'' Z'').ι
  have hinner : ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq') ≫
        idealSheafMap B S hS Z Z' g f hsq) ≫ (definingIdealSheaf B S hS X Z).ι =
      ((modulePullback B S hS g).map ((modulePullback B S hS g').map
          (definingIdealSheaf B S hS X'' Z'').ι) ≫
        (modulePullback B S hS g).map (structureModulePullbackMap B S hS g')) ≫
        structureModulePullbackMap B S hS g :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq)).trans
        ((Category.assoc _ _ _).symm.trans
          (eq_whisker ((((modulePullback B S hS g).map_comp
              (idealSheafMap B S hS Z' Z'' g' f' hsq')
              (definingIdealSheaf B S hS X' Z').ι).symm.trans
            (congrArg (modulePullback B S hS g).map
              (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z' Z'' g' f' hsq'))).trans
            ((modulePullback B S hS g).map_comp _ _)) _)))
  have hCC2 := (eq_whisker hCC ((modulePullback B S hS g).map
    ((modulePullback B S hS g').map (definingIdealSheaf B S hS X'' Z'').ι))).trans hnat.symm
  refine Eq.trans (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z''
    (g ≫ g') (f ≫ f') hsq'') ?_
  refine Eq.trans (whisker_eq _ (structureModulePullbackMap_comp B S hS g g')) ?_
  refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ hinner)).symm
  refine Eq.trans ?_ (whisker_eq
    ((modulePullbackCompIso B S hS g g').inv.app
      (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)
    (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker hCC2 _).symm
  exact (Category.assoc _ _ _).symm

/-! ### Invertibility of the conormal map of a composite -/

section Conormal

-- The two statements below compare `(g'^* ⋙ g^*).obj 𝓘''` with `g^*(g'^*𝓘'')`; unfolding the
-- inverse image to its construction does not terminate, and is not needed to see they agree.
attribute [local irreducible] modulePullback

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')
    (hsq'' : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      (f ≫ f') ≫ subspaceInclusion B S hS X'' Z'')

/-- The conormal map of the outer rectangle, with the inverse image along the inclusion of `Z`
of the two maps of defining ideal sheaves split off as a right factor.  The left factor is the
comparison of the outer rectangle followed by the composition comparison of [Stacks Project,
Tag 03LU] for the two vertical morphisms, and is therefore an isomorphism. -/
private theorem conormalMap_eq_outerComparison_comp :
    conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' =
      (conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' ≫
          (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
            ((modulePullbackCompIso B S hS g g').inv.app
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq') ≫
            idealSheafMap B S hS Z Z' g f hsq) :=
  (whisker_eq (conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')
      ((congrArg (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (idealSheafMap_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsq'')).trans
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map_comp _ _))).trans
    (Category.assoc _ _ _).symm

/-- The inverse image along `f` of the conormal map of the lower square, followed by the
conormal map of the upper square, with the same right factor split off.  The left factor is the
inverse image along `f` of the comparison of the lower square followed by the comparison of the
upper square, and is therefore an isomorphism.

The two maps of defining ideal sheaves are moved past the comparison of the upper square by its
naturality. -/
private theorem comp_conormalMap_eq_comparison_comp :
    (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalMap B S hS Z Z' g f hsq =
      ((modulePullback B S hS f).map (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq') ≫
            idealSheafMap B S hS Z Z' g f hsq) := by
  have hnat : (modulePullback B S hS f).map
          ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).map
            (idealSheafMap B S hS Z' Z'' g' f' hsq')) ≫
        conormalPullbackComparison B S hS Z Z' g f hsq =
      (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq')) :=
    (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.naturality
      (idealSheafMap B S hS Z' Z'' g' f' hsq')
  refine Eq.trans (eq_whisker ((modulePullback B S hS f).map_comp
    (conormalPullbackComparison B S hS Z' Z'' g' f' hsq')
    ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).map
      (idealSheafMap B S hS Z' Z'' g' f' hsq'))) (conormalMap B S hS Z Z' g f hsq)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine whisker_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hnat _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _
    ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map_comp _ _).symm


/-- Invertibility of the conormal map of the outer rectangle is equivalent to that of the
composite of the conormal maps of the two squares: both have the same right factor, and the
left factors are composites of comparison isomorphisms. -/
private theorem isIso_conormalMap_comp_iff_aux :
    IsIso (conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'') ↔
      IsIso ((modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalMap B S hS Z Z' g f hsq) := by
  have hcomp : IsIso ((modulePullbackCompIso B S hS g g').inv.app
      (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) :=
    inferInstanceAs (IsIso (((modulePullbackCompIso B S hS g g').app
      (definingIdealSheaf B S hS X'' Z'').toSheafOfModules).inv))
  have hleft : IsIso (conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' ≫
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
        ((modulePullbackCompIso B S hS g g').inv.app
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) :=
    IsIso.comp_isIso' (isIso_conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')
      inferInstance
  have hright : IsIso ((modulePullback B S hS f).map
      (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
      (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
        ((modulePullback B S hS g').obj
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) :=
    IsIso.comp_isIso'
      (@Functor.map_isIso _ _ _ _ _ _ _ _
        (isIso_conormalPullbackComparison B S hS Z' Z'' g' f' hsq'))
      (inferInstanceAs (IsIso (((conormalPullbackCompIso B S hS Z Z' g f hsq).app
        ((modulePullback B S hS g').obj
          (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)).hom)))
  refine ⟨fun hiso => ?_, fun hiso => ?_⟩
  · have hideal := @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hleft hiso
        (conormalMap_eq_outerComparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsq'').symm
    rw [comp_conormalMap_eq_comparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq']
    exact IsIso.comp_isIso' hright hideal
  · have hideal := @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hright hiso
        (comp_conormalMap_eq_comparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq').symm
    rw [conormalMap_eq_outerComparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsq'']
    exact IsIso.comp_isIso' hleft hideal

/-- **Invertibility of the conormal map of a composite descends to the two factors**, part (3)
of [Stacks Project, Tag 04G2] in the form invertibility consumes.  If the conormal map of the
outer rectangle is an isomorphism then so is the inverse image along `f` of the conormal map of
the lower square followed by the conormal map of the upper square.

Both composites have the inverse image along the inclusion of `Z` of the two maps of defining
ideal sheaves of [Stacks Project, Tag 04CP] as a right factor, and in both the left factor is a
composite of comparison isomorphisms; so the hypothesis makes that common right factor
invertible, and with it the second composite. -/
@[stacks 04G2 "invertibility of the conormal map of a composite, on the small étale site of an \
algebraic space"]
theorem isIso_comp_conormalMap_of_isIso_conormalMap
    (hiso : IsIso (conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')) :
    IsIso ((modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
      conormalMap B S hS Z Z' g f hsq) :=
  (isIso_conormalMap_comp_iff_aux ..).mp hiso

/-- **Invertibility of the conormal map of a composite and of its two factors agree**, part (3)
of [Stacks Project, Tag 04G2] in the form invertibility consumes.  The conormal map of the outer
rectangle is an isomorphism if and only if the inverse image along `f` of the conormal map of the
lower square followed by the conormal map of the upper square is one.

Both composites have the inverse image along the inclusion of `Z` of the two maps of defining
ideal sheaves of [Stacks Project, Tag 04CP] as a right factor, and in both the left factor is a
composite of comparison isomorphisms; so invertibility of either composite makes that common
right factor invertible, and with it the other composite.  Neither direction assumes anything:
the two composites differ by comparison isomorphisms only, which is part (3) of the tag in the
form that does not name the comparison. -/
theorem isIso_conormalMap_comp_iff :
    IsIso (conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'') ↔
      IsIso ((modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalMap B S hS Z Z' g f hsq) :=
  isIso_conormalMap_comp_iff_aux ..

/-- The shape of the composition formula for conormal maps, with every inverse-image functor,
module and comparison abstracted: the two factorizations `h1` and `h2` through the common right
factor `r`, and the pasting `h3` of the comparisons of the two squares, give the formula.

The conormal module `N''` is a separate variable, identified with the inverse image of the ideal
sheaf only through the equation `hN`, so that the arguments of an instance have literally the
types they are declared with. -/
private theorem comp_eq_of_paste {𝓜₂ 𝓩₂ 𝓩₁ 𝓩₀ 𝓜₁ 𝓧₀ : Type*} {_ : Category 𝓜₂}
    {_ : Category 𝓩₂} {_ : Category 𝓩₁} {_ : Category 𝓩₀} {_ : Category 𝓜₁}
    {_ : Category 𝓧₀} {I'' : 𝓜₂ ⥤ 𝓩₂} {F' : 𝓩₂ ⥤ 𝓩₁} {F : 𝓩₁ ⥤ 𝓩₀} {Fc : 𝓩₂ ⥤ 𝓩₀}
    {G' : 𝓜₂ ⥤ 𝓜₁} {I' : 𝓜₁ ⥤ 𝓩₁} {G : 𝓜₁ ⥤ 𝓧₀} {I : 𝓧₀ ⥤ 𝓩₀} {Gc : 𝓜₂ ⥤ 𝓧₀}
    (a : Fc ⟶ F' ⋙ F) (c' : I'' ⋙ F' ⟶ G' ⋙ I') (c : I' ⋙ F ⟶ G ⋙ I)
    (c'' : I'' ⋙ Fc ⟶ Gc ⋙ I) (b : Gc ⟶ G' ⋙ G) (J : 𝓜₂) (J₀ : 𝓧₀)
    (N'' : 𝓩₂) (K' : 𝓩₁) (hN : N'' = I''.obj J) (cmO : Fc.obj N'' ⟶ I.obj J₀)
    (cm' : F'.obj N'' ⟶ K') (cm : F.obj K' ⟶ I.obj J₀)
    (x : Fc.obj N'' ⟶ I.obj (Gc.obj J)) (y : F'.obj N'' ⟶ I'.obj (G'.obj J))
    (r : G.obj (G'.obj J) ⟶ J₀)
    (h1 : cmO = (x ≫ I.map (b.app J)) ≫ I.map r)
    (h2 : F.map cm' ≫ cm = (F.map y ≫ c.app (G'.obj J)) ≫ I.map r)
    (h3 : c''.app J ≫ I.map (b.app J) =
      (Functor.whiskerLeft I'' a ≫ Functor.whiskerRight c' F ≫ Functor.whiskerLeft G' c).app J)
    (hx : HEq x (c''.app J)) (hy : HEq y (c'.app J)) :
    cmO = a.app N'' ≫ F.map cm' ≫ cm := by
  subst hN
  have e : x ≫ I.map (b.app J) = a.app (I''.obj J) ≫ F.map y ≫ c.app (G'.obj J) := by
    rw [eq_of_heq hx, eq_of_heq hy]
    exact h3
  rw [h1, h2, e]
  simp only [Category.assoc]

/-- **The composition formula for conormal maps**, part (3) of [Stacks Project, Tag 04G2], for
closed subspaces of algebraic spaces.  For two vertically composable commutative squares of
closed subspaces, the conormal map `(f ≫ f')^*𝒞_{Z''/X''} ⟶ 𝒞_{Z/X}` of the outer rectangle is
the inverse image along `f` of the conormal map of the lower square followed by the conormal map
of the upper square, read through the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU].

Both sides have the inverse image along the inclusion of `Z` of the two maps of defining ideal
sheaves as a right factor, by `AlgebraicGeometry.Space.idealSheafMap_comp`; the two left factors
agree by the pasting `AlgebraicGeometry.Space.conormalPullbackCompIso_paste_app` of the
comparisons of the two squares. -/
@[stacks 04G2 "part (3), for closed subspaces of algebraic spaces",
  stacks 04G2 "part (3): the composition law for the conormal map, on the small étale site \
of an algebraic space"]
theorem conormalMap_comp :
    conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'' =
      (modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z'') ≫
        (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
          conormalMap B S hS Z Z' g f hsq :=
  comp_eq_of_paste (modulePullbackCompIso B S hS f f').inv
    (conormalPullbackCompIso B S hS Z' Z'' g' f' hsq').hom
    (conormalPullbackCompIso B S hS Z Z' g f hsq).hom
    (conormalPullbackCompIso B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'').hom
    (modulePullbackCompIso B S hS g g').inv
    (definingIdealSheaf B S hS X'' Z'').toSheafOfModules
    (definingIdealSheaf B S hS X Z).toSheafOfModules
    (conormalModule B S hS X'' Z'') (conormalModule B S hS X' Z') rfl
    (conormalMap B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')
    (conormalMap B S hS Z' Z'' g' f' hsq') (conormalMap B S hS Z Z' g f hsq)
    (conormalPullbackComparison B S hS Z Z'' (g ≫ g') (f ≫ f') hsq'')
    (conormalPullbackComparison B S hS Z' Z'' g' f' hsq')
    ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq') ≫
      idealSheafMap B S hS Z Z' g f hsq)
    (conormalMap_eq_outerComparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsq'')
    (comp_conormalMap_eq_comparison_comp B S hS g g' Z Z' Z'' f f' hsq hsq')
    (conormalPullbackCompIso_paste_app B S hS Z Z' Z'' g g' f f' hsq hsq' hsq''
      (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)
    HEq.rfl HEq.rfl

/-- **The composition formula for conormal maps, with the upper edge of the outer rectangle and
the composition comparison handed over in arguments.**  This is
`AlgebraicGeometry.Space.conormalMap_comp` restated so that a consumer whose goal spells the
upper edge of the outer rectangle as something other than `f ≫ f'` — a projection of an
iterated inverse image, say — never asks for the two spellings to be identified under a
`CategoryTheory.Functor.map` or a `CategoryTheory.NatTrans.app`.

Two crossings are moved into arguments.  The upper edge `fc` is a variable with its value given
by the equation `hfc`, which the statement is type-correct without, since the source of the
conormal map mentions `fc` only as an argument of `AlgebraicGeometry.Space.modulePullback`; and
the composition comparison of [Stacks Project, Tag 03LU] is a variable `e` with its value given
by a heterogeneous equality `he`, whose two types are then never compared in the statement at
all.  At a use site both are discharged by `rfl` and `HEq.rfl` once `fc` is `f ≫ f'`, and by one
equation of morphisms otherwise. -/
theorem conormalMap_comp_of_eq
    (fc : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS)) (hfc : fc = f ≫ f')
    (hsqc : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      fc ≫ subspaceInclusion B S hS X'' Z'')
    (e : (modulePullback B S hS fc).obj (conormalModule B S hS X'' Z'') ⟶
      (modulePullback B S hS f).obj
        ((modulePullback B S hS f').obj (conormalModule B S hS X'' Z'')))
    (he : HEq e
      ((modulePullbackCompIso B S hS f f').inv.app (conormalModule B S hS X'' Z''))) :
    conormalMap B S hS Z Z'' (g ≫ g') fc hsqc =
      e ≫ (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalMap B S hS Z Z' g f hsq := by
  subst hfc
  obtain rfl := eq_of_heq he
  exact conormalMap_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsqc

/-- **The composition formula for conormal maps, with the upper edge of the outer rectangle a
variable and the composition comparison read off that variable's defining equation.**  This is
`AlgebraicGeometry.Space.conormalMap_comp_of_eq` with the comparison of [Stacks Project,
Tag 03LU] supplied rather than quantified: `AlgebraicGeometry.Space.modulePullbackTriangle` is
the comparison of that tag *indexed by an equation* `f ≫ f' = fc`, so its source is the inverse
image along `fc` as the consumer spells it, and the consumer has nothing to discharge.

Why that matters.  The inverse image along a composite morphism is free under a
`CategoryTheory.Functor.obj` and fatal under a `CategoryTheory.Functor.map`, which reduces its
projection first; and `AlgebraicGeometry.Space.modulePullbackCompIso` at an edge names the
inverse image along that edge as a factor of a composite *functor*.  A consumer whose own upper
edge is a second spelling of `f ≫ f'` therefore cannot afford either the comparison of that tag
at its own edge or the heterogeneous equality that
`AlgebraicGeometry.Space.conormalMap_comp_of_eq` asks for; with the comparison taken from the
equation, no two spellings of an inverse image ever meet.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftSheaf.lean` record the timings, the
minimal pair that isolates `CategoryTheory.Functor.map` as the deciding position, and what the
restriction stability of condition (3) of [Stacks Project, Tag 061A] still waits on. -/
theorem conormalMap_comp_triangle
    (fc : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS)) (hfc : f ≫ f' = fc)
    (hsqc : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      fc ≫ subspaceInclusion B S hS X'' Z'') :
    conormalMap B S hS Z Z'' (g ≫ g') fc hsqc =
      (modulePullbackTriangle B S hS hfc).hom.app (conormalModule B S hS X'' Z'') ≫
        (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
          conormalMap B S hS Z Z' g f hsq := by
  subst hfc
  refine Eq.trans (conormalMap_comp B S hS g g' Z Z' Z'' f f' hsq hsq' hsqc) ?_
  refine congrArg (fun m => m ≫ (modulePullback B S hS f).map
    (conormalMap B S hS Z' Z'' g' f' hsq') ≫ conormalMap B S hS Z Z' g f hsq) ?_
  exact (congrArg (fun i : modulePullback B S hS (f ≫ f') ≅
      modulePullback B S hS f' ⋙ modulePullback B S hS f =>
    i.hom.app (conormalModule B S hS X'' Z'')) (modulePullbackTriangle_rfl f f')).symm

/-- **The composition formula for conormal maps, with the comparison of the outer rectangle
handed over as a natural transformation and its value in a separate equation.**  This is
`AlgebraicGeometry.Space.conormalMap_comp_triangle` with
`AlgebraicGeometry.Space.modulePullbackTriangle` abstracted out of the conclusion: the
comparison is a variable natural transformation `t`, and the equation `ht` fixing its value is a
hypothesis of its own.  It is strictly more general than
`AlgebraicGeometry.Space.conormalMap_comp_triangle`, which is its instance at
`t := (modulePullbackTriangle B S hS hfc).hom` and `ht := rfl`.

**It does not make the composite-edge case cheaper.**  This variant suggests itself on the
reading that a consumer whose edge `f'` of the lower square is a composite `p ≫ a` cannot afford
the comparison at that edge.  That reading is false: at abstract closed subspaces the law at
`f' := p ≫ a`, with `fc := (r ≫ p) ≫ a` and `hfc := (CategoryTheory.Category.assoc r p a).symm`,
compiles and kernel-checks freely, while *this* variant at the same data is a
`(kernel) deterministic timeout` — abstracting the comparison into a variable and substituting it
back is strictly more expensive than naming it.  The same holds with the comparison abstracted as
an isomorphism of functors rather than as a natural transformation; the hypothesis types
themselves are free, so the cost is the abstraction, not the equation.  What the consumer
actually meets, recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftSheaf.lean`, is a spelling of
`AlgebraicGeometry.Space.ClosedSubspaces` and not a composite edge at all.

The equation is kept at the level of natural transformations, not of their components, in the
standing discipline of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean`. -/
theorem conormalMap_comp_triangle_of_eq
    (fc : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS)) (hfc : f ≫ f' = fc)
    (hsqc : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      fc ≫ subspaceInclusion B S hS X'' Z'')
    (t : modulePullback B S hS fc ⟶
      modulePullback B S hS f' ⋙ modulePullback B S hS f)
    (ht : t = (modulePullbackTriangle B S hS hfc).hom) :
    conormalMap B S hS Z Z'' (g ≫ g') fc hsqc =
      t.app (conormalModule B S hS X'' Z'') ≫
        (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
          conormalMap B S hS Z Z' g f hsq := by
  subst ht
  exact conormalMap_comp_triangle B S hS g g' Z Z' Z'' f f' hsq hsq' fc hfc hsqc

/-- **The composition formula for conormal maps, with the ambient algebraic spaces of the three
closed subspaces handed over in arguments.**  This is
`AlgebraicGeometry.Space.conormalMap_comp_triangle` restated so that a consumer whose goal spells
those ambient spaces otherwise than as `⟨Z.1.toFunctor, Z.2.1⟩` of the subspace the law is
instantiated at never asks for the two spellings to be identified inside a written-out equation
of morphisms of modules.

Every object and morphism of the conclusion is a variable — the spaces `𝒵`, `𝒵'`, `𝒵''`, the
edges `fs`, `fs'`, `fsc`, the modules `N`, `N'`, `N''` and the three conormal maps `cm`, `cm'`,
`cmc` — and each carries its value in an equation of spaces or a heterogeneous equality, so that
the whole statement is type-correct before any of them is identified with what the law produces.
The crossing a consumer pays is therefore at a `Quiver.Hom` of
`AlgebraicGeometry.Space.Modules`, where the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DeformationLiftSheaf.lean` measure it to be free, rather
than inside the law's conclusion, where they measure it to be unaffordable.

The conclusion is a homogeneous equation, unlike that of
`AlgebraicGeometry.Space.conormalMap_comp_of_spaces` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/SectionsConormalAction.lean`, which applies
the same discipline to `AlgebraicGeometry.Space.conormalMap_comp`: that lemma abstracts the one
ambient space of the lower subspace *twice*, once for the outer rectangle and once for the lower
square, so its two sides are read over two variables and only a heterogeneous conclusion
typechecks.  Here the source of the outer rectangle and of the lower square is the single
variable `𝒵`, and the upper edge of the outer rectangle is a variable `fsc` fixed by the
equation `hfsc` rather than the composite `fs ≫ fs'`, so that the comparison of [Stacks Project,
Tag 03LU] enters as `AlgebraicGeometry.Space.modulePullbackTriangle` at `fsc`.  Both are what a
consumer whose own chase states its hypotheses as equations of morphisms of modules needs.

At a use site every equation is `rfl` or `HEq.rfl` once the law's own spelling is supplied. -/
theorem conormalMap_comp_triangle_of_spaces
    (fc₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsqc₀ : subspaceInclusion B S hS X Z ≫ g ≫ g' =
      fc₀ ≫ subspaceInclusion B S hS X'' Z'')
    (𝒵 𝒵' 𝒵'' : AlgebraicSpaces B S hS)
    (h𝒵 : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) = 𝒵)
    (h𝒵' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) = 𝒵')
    (h𝒵'' : (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS) = 𝒵'')
    (fs : 𝒵 ⟶ 𝒵') (fs' : 𝒵' ⟶ 𝒵'') (fsc : 𝒵 ⟶ 𝒵'') (hfsc : fs ≫ fs' = fsc)
    {N : Modules.{u, u} B S hS 𝒵.1 𝒵.2} {N' : Modules.{u, u} B S hS 𝒵'.1 𝒵'.2}
    {N'' : Modules.{u, u} B S hS 𝒵''.1 𝒵''.2}
    (cm : (modulePullback B S hS fs).obj N' ⟶ N)
    (cm' : (modulePullback B S hS fs').obj N'' ⟶ N')
    (cmc : (modulePullback B S hS fsc).obj N'' ⟶ N)
    (hN : HEq N (conormalModule B S hS X Z)) (hN' : HEq N' (conormalModule B S hS X' Z'))
    (hN'' : HEq N'' (conormalModule B S hS X'' Z''))
    (hfs : HEq fs f) (hfs' : HEq fs' f') (hfsc₀ : HEq fsc fc₀)
    (hcm : HEq cm (conormalMap B S hS Z Z' g f hsq))
    (hcm' : HEq cm' (conormalMap B S hS Z' Z'' g' f' hsq'))
    (hcmc : HEq cmc (conormalMap B S hS Z Z'' (g ≫ g') fc₀ hsqc₀)) :
    cmc = (modulePullbackTriangle B S hS hfsc).hom.app N'' ≫
      (modulePullback B S hS fs).map cm' ≫ cm := by
  subst h𝒵
  subst h𝒵'
  subst h𝒵''
  obtain rfl := eq_of_heq hfs
  obtain rfl := eq_of_heq hfs'
  obtain rfl := eq_of_heq hfsc₀
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hN'
  obtain rfl := eq_of_heq hN''
  obtain rfl := eq_of_heq hcm
  obtain rfl := eq_of_heq hcm'
  obtain rfl := eq_of_heq hcmc
  exact conormalMap_comp_triangle B S hS g g' Z Z' Z'' _ _ hsq hsq' _ hfsc hsqc₀

end Conormal

end AlgebraicGeometry.Space

end
