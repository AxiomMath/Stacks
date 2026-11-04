module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# Equal conormal maps force the two comorphisms to agree on the ideal of the target

Let `Z ⊆ X` be a first-order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, let `W₀ ⊆ W` be a closed subspace of a second algebraic space, with inclusion
`j : W₀ ⟶ W`, let `f : Z ⟶ W₀` and let `c, c' : X ⟶ W` be two morphisms with
`i ≫ c = f ≫ j = i ≫ c'`.  Each square has its canonical map of conormal modules
`f^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP], `AlgebraicGeometry.Space.conormalMap`.

This file proves hypothesis (2) of [Stacks Project, Tag 0618] in the form the difference of two
lifts consumes: **if the two conormal maps are equal, then the two comorphisms of `c` and `c'`,
read through the thickening, agree on every local section of the defining ideal of `W₀`**, and
so do their transports to the small étale site of `W₀`
(`AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_conormalMap_eq`), which is
the field `app_eq_of_app_eq_zero` of the datum
`AlgebraicGeometry.Space.restrictedLiftDifferenceData`.

## The argument

On a local section `a` of the ideal `𝓘'` of `W₀`, the comorphism of `c` read through the
thickening is the pullback of `a` along `c`, which lies in the ideal `𝓘` of `Z`, followed by the
unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`.  Both steps are expressed by the conormal map:

* the pullback of a function of the ideal is the map of ideal sheaves `c^*𝓘' ⟶ 𝓘` of
  `AlgebraicGeometry.Space.idealSheafMap`, transposed
  (`AlgebraicGeometry.Space.modulePushforward_map_ι_homEquiv_idealSheafMap_val_app`), which is the
  content of `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`;
* the unit of `i^* ⊣ i_*` at `𝓘` identifies `𝓘` with `i_*𝒞_{Z/X}`, and composing with the
  inclusion `AlgebraicGeometry.Space.firstOrderConormalSetInclusion` of the conormal module into
  `i^{-1}𝒪_X` gives back the unit of the structure sheaf on `𝓘`
  (`AlgebraicGeometry.Space.unit_comp_pushforward_map_conormalSetInclusion`).

So the comorphism on `𝓘'` is the double transpose of the conormal map along `f^* ⊣ f_*` and
`j^* ⊣ j_*` followed by that inclusion
(`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_app_definingIdealSheaf_ι`); the
double transpose is computed from the definition of the conormal map in
`AlgebraicGeometry.Space.homEquiv_homEquiv_conormalMap`.  Equal conormal maps therefore give
equal values.

## Main definitions

* `AlgebraicGeometry.Space.firstOrderConormalSetInclusion`: the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X`
  of the conormal module of a first-order thickening, on sheaves of sets, pinned by the unit.

## Main results

* `AlgebraicGeometry.Space.homEquiv_homEquiv_conormalMap`: the double transpose of the
  conormal map.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_app_definingIdealSheaf_ι`: the
  comorphism read through the thickening on a section of the ideal of `W₀`, through the
  conormal map.
* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_app_eq_of_conormalMap_eq` and
  `AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_conormalMap_eq`:
  **hypothesis (2) of [Stacks Project, Tag 0618]**: equal conormal maps give comorphisms which
  agree on the sections killed by the reduction to `W₀`.

## Implementation notes

**Spelling of the composites.**  The commutative square `i ≫ c = f ≫ j` is stated in the
library with its composites elaborated in the full subcategory underlying
`AlgebraicGeometry.AlgebraicSpaces`, while `AlgebraicGeometry.Space.modulePullbackCompIso` and
`AlgebraicGeometry.Space.modulePushforwardCompIso` form theirs in
`AlgebraicGeometry.AlgebraicSpaces`
itself.  The two are definitionally equal, but a transport along the square written in one
spelling and composed with a comparison written in the other is beyond the kernel's budget.  So
the square is restated once in the second spelling
(`AlgebraicGeometry.Space.subspaceInclusion_comp_eq_comp_subspaceInclusion`) and every transport
below is taken along that restatement; the local notation `⊚` is composition in
`AlgebraicGeometry.AlgebraicSpaces`.

**Every crossing is made at variable spaces.**  The comparisons between the direct image of
modules and the direct image of their underlying sheaves of sets, and between the two forms of
the direct image of a composite, are definitional but expensive to discover at the concrete
spaces of the square.  They are therefore made inside statements whose spaces and morphisms are
variables (`AlgebraicGeometry.Space.pushforward_map_app_val_app_comp_transpose`,
`AlgebraicGeometry.Space.eqToHom_app_pushforward_map_eq`) and only instantiated afterwards.

**The inclusion of the conormal module is rebuilt on sheaves of sets.**  The library's
inclusion `AlgebraicGeometry.Space.conormalInverseImageι` is defined through a comparison of two
spellings of the direct image whose components are a transport along an opaque equality, so
its relation to the unit of `i^* ⊣ i_*` is not available on sections.  The argument only needs
an inclusion which does not depend on `c`, and
`AlgebraicGeometry.Space.firstOrderConormalSetInclusion` is the one whose relation to the unit
holds by construction.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1) (c : X ⟶ W)
  (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The commutative square of inclusions, with its composites formed in
`AlgebraicGeometry.AlgebraicSpaces`.**  This is the hypothesis itself; restating it fixes the
spelling of the two composites to the one the composition comparisons of
[Stacks Project, Tag 03LU] use.  See the implementation notes. -/
theorem subspaceInclusion_comp_eq_comp_subspaceInclusion
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀) :
    @Eq (_ ⟶ W)
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ (subspaceInclusion B S hS X Z) c)
      (@CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _ f
        (subspaceInclusion B S hS W W₀)) :=
  hsq

attribute [local irreducible] modulePullback

/-- Composition in `AlgebraicGeometry.AlgebraicSpaces`; see the implementation notes. -/
local notation:80 a " ⊚ " b => @CategoryStruct.comp (AlgebraicSpaces _ _ _) _ _ _ _ a b

/-! ### The double transpose of the conormal map -/

/-- Transposing a morphism out of an inverse image along `e₁` through a transport to the inverse
image along an equal morphism `e₂`. -/
private theorem homEquiv_eqToHom_modulePullback_app_comp {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS} {e₁ e₂
    : Y₁ ⟶ Y₂}
    (p : e₁ = e₂) (F₁ : Modules.{u, u} B S hS Y₂.1 Y₂.2 ⥤ Modules.{u, u} B S hS Y₃.1 Y₃.2)
    (F₂ : Modules.{u, u} B S hS Y₃.1 Y₃.2 ⥤ Modules.{u, u} B S hS Y₁.1 Y₁.2)
    (α : modulePullback B S hS e₂ ⟶ F₁ ⋙ F₂) (M : Modules.{u, u} B S hS Y₂.1 Y₂.2)
    (N : Modules.{u, u} B S hS Y₁.1 Y₁.2) (φ : F₂.obj (F₁.obj M) ⟶ N) :
    (modulePullbackAdjunction B S hS e₁).homEquiv M N
        ((eqToHom (congrArg (fun e => modulePullback B S hS e) p) ≫ α).app M ≫ φ) =
      (modulePullbackAdjunction B S hS e₂).homEquiv M N (α.app M ≫ φ) ≫
        eqToHom (congrArg (fun e => (modulePushforward B S hS e).obj N) p.symm) := by
  subst p
  simp

/-- **The comparison of a commutative square, after the composition comparison along its upper
edge.**  It is the transport along the square followed by the inverse composition comparison
along its lower edge. -/
theorem modulePullbackCompIso_inv_comp_conormalPullbackCompIso_hom
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀) :
    (modulePullbackCompIso B S hS f (subspaceInclusion B S hS W W₀)).inv ≫
      (conormalPullbackCompIso B S hS Z W₀ c f hsq).hom =
      eqToHom (congrArg (fun h ↦ modulePullback B S hS h)
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm) ≫
        (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv := by
  rw [show (conormalPullbackCompIso B S hS Z W₀ c f hsq).hom =
      (modulePullbackCompIso B S hS f (subspaceInclusion B S hS W W₀)).hom ≫
        eqToHom (congrArg (fun h ↦ modulePullback B S hS h)
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm) ≫
        (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv from rfl,
    Iso.inv_hom_id_assoc]

/-- The first step of
`AlgebraicGeometry.Space.homEquiv_homEquiv_conormalPullbackCompIso_hom_app_comp`:
the two transposes become one transpose along the composite. -/
private theorem homEquiv_homEquiv_conormalPullbackCompIso_eq_homEquiv_comp
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (M : Modules.{u, u} B S hS W.1 W.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS c).obj M ⟶ N) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS W W₀)).homEquiv _ _
        ((modulePullbackAdjunction B S hS f).homEquiv _ _
          ((conormalPullbackCompIso B S hS Z W₀ c f hsq).hom.app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ)) ≫
        (modulePushforwardCompIso B S hS f (subspaceInclusion B S hS W W₀)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N) =
      (modulePullbackAdjunction B S hS (f ⊚ subspaceInclusion B S hS W W₀)).homEquiv _ _
        (((modulePullbackCompIso B S hS f (subspaceInclusion B S hS W W₀)).inv ≫
          (conormalPullbackCompIso B S hS Z W₀ c f hsq).hom).app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) :=
  (homEquiv_modulePullbackCompIso_inv_app_comp B S hS f (subspaceInclusion B S hS W W₀) M _
    _).symm.trans (congrArg ((modulePullbackAdjunction B S hS
      (f ⊚ subspaceInclusion B S hS W W₀)).homEquiv _ _)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _) (NatTrans.comp_app _ _ M).symm)))

/-- The third step: the transport along the square is moved out of the transpose. -/
private theorem homEquiv_eqToHom_comp_modulePullbackCompIso_inv_app_comp
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (M : Modules.{u, u} B S hS W.1 W.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS c).obj M ⟶ N) :
      (modulePullbackAdjunction B S hS (f ⊚ subspaceInclusion B S hS W W₀)).homEquiv _ _
        ((eqToHom (congrArg (fun h ↦ modulePullback B S hS h)
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm) ≫
        (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv).app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) =
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z ⊚ c)).homEquiv _ _
          ((modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv.app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) ≫
        eqToHom (congrArg (fun e =>
          (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N))
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm) :=
  homEquiv_eqToHom_modulePullback_app_comp B S hS
    (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm
      (modulePullback B S hS c) (modulePullback B S hS (subspaceInclusion B S hS X Z))
      (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv M
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N)
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ)

/-- The second step: the comparison of the square is moved past the composition comparison. -/
private theorem homEquiv_comp_conormalPullbackCompIso_eq_homEquiv_eqToHom_comp
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (M : Modules.{u, u} B S hS W.1 W.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS c).obj M ⟶ N) :
      (modulePullbackAdjunction B S hS (f ⊚ subspaceInclusion B S hS W W₀)).homEquiv _ _
        (((modulePullbackCompIso B S hS f (subspaceInclusion B S hS W W₀)).inv ≫
          (conormalPullbackCompIso B S hS Z W₀ c f hsq).hom).app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) =
      (modulePullbackAdjunction B S hS (f ⊚ subspaceInclusion B S hS W W₀)).homEquiv _ _
        ((eqToHom (congrArg (fun h ↦ modulePullback B S hS h)
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm) ≫
        (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv).app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) := by
  rw [modulePullbackCompIso_inv_comp_conormalPullbackCompIso_hom]

/-- The fourth step: the transpose along the composite `i ≫ c`. -/
private theorem homEquiv_modulePullbackCompIso_inv_app_comp_map
    (M : Modules.{u, u} B S hS W.1 W.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS c).obj M ⟶ N) :
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z ⊚ c)).homEquiv _ _
          ((modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) c).inv.app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ) =
      (modulePullbackAdjunction B S hS c).homEquiv _ _ φ ≫
        (modulePushforward B S hS c).map
          ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app N) ≫
        (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N) := by
  rw [homEquiv_modulePullbackCompIso_inv_app_comp,
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv_unit,
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit_naturality,
    (modulePullbackAdjunction B S hS c).homEquiv_naturality_right, Category.assoc]

/-- **The double transpose of a morphism out of the comparison of a commutative square.**  For a
morphism `φ : c^*M ⟶ N`, the comparison `f^*j^*M ⟶ i^*c^*M` of the square followed by `i^*φ`,
transposed along `f^* ⊣ f_*` and then `j^* ⊣ j_*` and read through the composition comparison, is
the transpose of `φ` along `c^* ⊣ c_*` followed by the direct image of the unit of `i^* ⊣ i_*`
and the composition comparison, transported along the square. -/
theorem homEquiv_homEquiv_conormalPullbackCompIso_hom_app_comp
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (M : Modules.{u, u} B S hS W.1 W.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (φ : (modulePullback B S hS c).obj M ⟶ N) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS W W₀)).homEquiv _ _
        ((modulePullbackAdjunction B S hS f).homEquiv _ _
          ((conormalPullbackCompIso B S hS Z W₀ c f hsq).hom.app M ≫
            (modulePullback B S hS (subspaceInclusion B S hS X Z)).map φ)) ≫
        (modulePushforwardCompIso B S hS f (subspaceInclusion B S hS W W₀)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N) =
      ((modulePullbackAdjunction B S hS c).homEquiv _ _ φ ≫
        (modulePushforward B S hS c).map
          ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app N) ≫
        (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N)) ≫
        eqToHom (congrArg (fun e =>
          (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj N))
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm) :=
  (homEquiv_homEquiv_conormalPullbackCompIso_eq_homEquiv_comp B S hS Z W₀ c f hsq M N φ).trans
    ((homEquiv_comp_conormalPullbackCompIso_eq_homEquiv_eqToHom_comp B S hS Z W₀ c f hsq M N
      φ).trans
    ((homEquiv_eqToHom_comp_modulePullbackCompIso_inv_app_comp B S hS Z W₀ c f hsq M N φ).trans
      (congrArg (fun t => t ≫ _)
        (homEquiv_modulePullbackCompIso_inv_app_comp_map B S hS Z c M N φ))))

/-- **The double transpose of the conormal map of [Stacks Project, Tag 04CP].**  Transposed along
`f^* ⊣ f_*` and `j^* ⊣ j_*` and read through the composition comparison, the conormal map of the
square is the transpose `𝓘' ⟶ c_*𝓘` of the map of ideal sheaves, followed by the direct image of
the unit `𝓘 ⟶ i_*𝒞_{Z/X}` and the composition comparison, transported along the square. -/
theorem homEquiv_homEquiv_conormalMap
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS W W₀)).homEquiv _ _
        ((modulePullbackAdjunction B S hS f).homEquiv _ _
          (conormalMap B S hS Z W₀ c f hsq)) ≫
        (modulePushforwardCompIso B S hS f (subspaceInclusion B S hS W W₀)).hom.app
          ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
            (definingIdealSheaf B S hS X Z).toSheafOfModules) =
      ((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq) ≫
          (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS
            (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)) ≫
        eqToHom (congrArg (fun e =>
          (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules))
          (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm) := by
  rw [conormalMap, conormalPullbackComparison]
  exact homEquiv_homEquiv_conormalPullbackCompIso_hom_app_comp B S hS Z W₀ c f hsq _ _ _

/-! ### A sections chase at variable spaces -/

/-- A composite of two morphisms of modules, on sections. -/
private theorem comp_val_app_modules {Y : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ : Modules.{u, u} B S hS Y.1 Y.2}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : M₁.val.obj V) :
    (a ≫ b).val.app V x = b.val.app V (a.val.app V x) :=
  rfl

/-- A composite of three morphisms of modules, on sections. -/
private theorem comp3_val_app_modules {Y : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ M₄ : Modules.{u, u} B S hS Y.1 Y.2}
    (a : M₁ ⟶ M₂) (b : M₂ ⟶ M₃) (d : M₃ ⟶ M₄) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : M₁.val.obj V) :
    (a ≫ b ≫ d).val.app V x = d.val.app V (b.val.app V (a.val.app V x)) :=
  rfl

section Generic

variable {A X' W' : AlgebraicSpaces B S hS}

/-- **The sections chase, at variable spaces.**  Let `ψ : P ⟶ c_*N` be a morphism of modules
whose composite with the direct image of an inclusion `ιN : N ⟶ 𝒪_{X'}` is, on sections, the
structure map of `c` after an inclusion `ιP : P ⟶ 𝒪_{W'}`, and let `γ` be a morphism of sheaves
of sets out of the underlying sheaf of `i^*N` which composes with the unit of `i^* ⊣ i_*` to give
the unit of `i^{-1} ⊣ i_*` after `ιN`.  Then `γ`, pushed forward along `i ≫ c`, applied to
`ψ` followed by the unit and the composition comparison, is the structure map of `c` followed by
the direct image of the unit `𝒪_{X'} ⟶ i_*i^{-1}𝒪_{X'}` and the composition comparison, on every
section of `P`. -/
private theorem pushforward_map_app_val_app_comp_transpose (i : A ⟶ X') (c : X' ⟶ W')
    (N : Modules.{u, u} B S hS X'.1 X'.2) (P : Modules.{u, u} B S hS W'.1 W'.2)
    (ψ : P ⟶ (modulePushforward B S hS c).obj N)
    (ιP : P ⟶ SheafOfModules.unit (structureRingSheaf B S hS W'))
    (ιN : N ⟶ SheafOfModules.unit (structureRingSheaf B S hS X'))
    (γ : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj
      ((modulePullback B S hS i).obj N) ⟶
      (smallToposMorphismTypeU B S hS i).inverseImage.obj (structureSetSheaf B S hS X'))
    (hγ : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS i).unit.app N) ≫
        (smallToposMorphismTypeU B S hS i).pushforward.map γ =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map ιN ≫
        (smallToposMorphismTypeU B S hS i).adj.unit.app (structureSetSheaf B S hS X'))
    (hψ : ∀ (V : (SmallEtale B S hS W'.1)ᵒᵖ) (s : P.val.obj V),
      ((modulePushforward B S hS c).map ιN).val.app V (ψ.val.app V s) =
        (structureSharpSet B S hS c).hom.app V (ιP.val.app V s))
    (V : (SmallEtale B S hS W'.1)ᵒᵖ) (s : P.val.obj V) :
    ((smallToposMorphismTypeU B S hS (i ≫ c)).pushforward.map γ).hom.app V
        ((ψ ≫ (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS i).unit.app N) ≫
          (modulePushforwardCompIso B S hS i c).hom.app
            ((modulePullback B S hS i).obj N)).val.app V s) =
      ((smallToposMorphismTypeU_comp B S hS i c).hom.app
          ((smallToposMorphismTypeU B S hS i).inverseImage.obj
            (structureSetSheaf B S hS X'))).hom.app V
        (((smallToposMorphismTypeU B S hS c).pushforward.map
          ((smallToposMorphismTypeU B S hS i).adj.unit.app (structureSetSheaf B S hS X'))).hom.app
            V ((structureSharpSet B S hS c).hom.app V (ιP.val.app V s))) := by
  rw [comp3_val_app_modules B S hS, modulePushforwardCompIso_hom_app_val_app]
  refine (congrArg (fun m => m.hom.app V
      (((modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS i).unit.app N)).val.app
        V (ψ.val.app V s)))
    ((smallToposMorphismTypeU_comp B S hS i c).hom.naturality γ).symm).trans ?_
  refine congrArg (fun y => ((smallToposMorphismTypeU_comp B S hS i c).hom.app
          ((smallToposMorphismTypeU B S hS i).inverseImage.obj
            (structureSetSheaf B S hS X'))).hom.app V y) ?_
  rw [← hψ]
  refine (congrArg (fun m => m.hom.app V (ψ.val.app V s))
    ((smallToposMorphismTypeU B S hS c).pushforward.map_comp
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map
        ((modulePullbackAdjunction B S hS i).unit.app N))
      ((smallToposMorphismTypeU B S hS i).pushforward.map γ))).symm.trans ?_
  refine (congrArg (fun m => ((smallToposMorphismTypeU B S hS c).pushforward.map m).hom.app V
    (ψ.val.app V s)) hγ).trans ?_
  exact congrArg (fun m => m.hom.app V (ψ.val.app V s))
    ((smallToposMorphismTypeU B S hS c).pushforward.map_comp
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map ιN)
      ((smallToposMorphismTypeU B S hS i).adj.unit.app (structureSetSheaf B S hS X')))

/-- A transport between direct images along equal morphisms commutes with the direct image of
a morphism into `i^{-1}𝒪`, on sections; stated at variable spaces. -/
private theorem eqToHom_app_pushforward_map_eq {A X' W' : AlgebraicSpaces B S hS} (i : A ⟶ X')
    {e₁ e₂ : A ⟶ W'} (p : e₁ = e₂) (M : Modules.{u, u} B S hS A.1 A.2)
    (γ : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS A)).obj M ⟶
      (smallToposMorphismTypeU B S hS i).inverseImage.obj (structureSetSheaf B S hS X'))
    (V : (SmallEtale B S hS W'.1)ᵒᵖ) (x : ((modulePushforward B S hS e₁).obj M).val.obj V) :
    (eqToHom (congrArg (fun m => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS W'.1) (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS i)) p)).hom.app V
        (((smallToposMorphismTypeU B S hS e₁).pushforward.map γ).hom.app V x) =
      ((smallToposMorphismTypeU B S hS e₂).pushforward.map γ).hom.app V
        ((eqToHom (congrArg (fun e => (modulePushforward B S hS e).obj M) p)).val.app V x) := by
  subst p
  rfl

end Generic

/-- The underlying morphism of sheaves of sets of a morphism of sheaves of rings, on
sections. -/
private theorem sheafCompose_forget_map_hom_app {Y : AlgebraicSpaces B S hS}
    {R R' : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}} (φ : R ⟶ R')
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : ToType (R.obj.obj V)) :
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (CategoryTheory.forget RingCat.{u})).map
        φ).hom.app V x = φ.hom.app V x :=
  rfl

/-! ### The inclusion of the conormal module, on sheaves of sets -/

/-- **The inclusion of the conormal module of a first-order thickening into `i^{-1}𝒪_X`, on
sheaves of sets.**  The direct image of sheaves of sets along the inclusion `i` of a closed
subspace is fully faithful, and this is the preimage of the inclusion
`AlgebraicGeometry.Space.firstOrderConormalModuleι : i_*𝒞_{Z/X} ⟶ 𝒪_X` followed by the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X`.  It is pinned by
`AlgebraicGeometry.Space.pushforward_map_firstOrderConormalSetInclusion`. -/
noncomputable def firstOrderConormalSetInclusion (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ⟶
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage.obj
        (structureSetSheaf B S hS X) :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2).preimage
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (firstOrderConormalModuleι B S hS Z hZ) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
        (structureSetSheaf B S hS X))

/-- The defining property of `AlgebraicGeometry.Space.firstOrderConormalSetInclusion`. -/
theorem pushforward_map_firstOrderConormalSetInclusion (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ) =
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (firstOrderConormalModuleι B S hS Z hZ) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
        (structureSetSheaf B S hS X) :=
  (fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
        (subspaceInclusion B S hS X Z) Z.2.2).map_preimage _

/-- The unit `𝓘 ⟶ i_*𝒞_{Z/X}` of a first-order thickening followed by the inclusion
`i_*𝒞_{Z/X} ⟶ 𝒪_X` is the inclusion of the defining ideal sheaf.  This is
`AlgebraicGeometry.Space.firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι` with the
isomorphism replaced by its underlying unit. -/
theorem modulePullbackAdjunction_unit_comp_firstOrderConormalModuleι
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        firstOrderConormalModuleι B S hS Z hZ =
      (definingIdealSheaf B S hS X Z).ι :=
  firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι B S hS Z hZ

/-- The unit of `i^* ⊣ i_*` at the defining ideal, followed by the direct image of the
inclusion of the conormal module, through the inclusion of
`AlgebraicGeometry.Space.firstOrderConormalModuleι`. -/
private theorem unit_comp_pushforward_map_conormalSetInclusion_eq_comp
    (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ) =
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
            firstOrderConormalModuleι B S hS Z hZ) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
        (structureSetSheaf B S hS X) :=
  (congrArg (fun t => (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫ t)
      (pushforward_map_firstOrderConormalSetInclusion B S hS Z hZ)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X Z)).adj.unit.app (structureSetSheaf B S hS X))
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm))

/-- **The inclusion of the conormal module is the unit on the defining ideal.**  The unit
`𝓘 ⟶ i_*𝒞_{Z/X}` followed by the direct image of
`AlgebraicGeometry.Space.firstOrderConormalSetInclusion` is the inclusion of the defining ideal
followed by the unit `𝒪_X ⟶ i_*i^{-1}𝒪_X`, on sheaves of sets. -/
theorem unit_comp_pushforward_map_conormalSetInclusion (hZ : IsFirstOrderThickening B S hS X Z.1) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ) =
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (definingIdealSheaf B S hS X Z).ι ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
        (structureSetSheaf B S hS X) :=
  (unit_comp_pushforward_map_conormalSetInclusion_eq_comp B S hS Z hZ).trans
    (congrArg (fun m => (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map m ≫
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
        (structureSetSheaf B S hS X))
          (modulePullbackAdjunction_unit_comp_firstOrderConormalModuleι B S hS Z hZ))

/-! ### The comorphism on the ideal of the target, through the conormal map -/

/-- **The transposed map of defining ideal sheaves is the comorphism, on sections.**  The
transpose `𝓘' ⟶ c_*𝓘` of `AlgebraicGeometry.Space.idealSheafMap`, followed by the direct image
of the inclusion `𝓘 ⊆ 𝒪_X`, is the structure map `c^♯` of [Stacks Project, Tag 03G8] on the
sections of `𝓘'`. -/
theorem modulePushforward_map_ι_homEquiv_idealSheafMap_val_app
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    ((modulePushforward B S hS c).map (definingIdealSheaf B S hS X Z).ι).val.app V
        (((modulePullbackAdjunction B S hS c).homEquiv _ _
          (idealSheafMap B S hS Z W₀ c f hsq)).val.app V s) =
      (structureSharpSet B S hS c).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  have key : (modulePullbackAdjunction B S hS c).homEquiv _ _
        (idealSheafMap B S hS Z W₀ c f hsq) ≫
        (modulePushforward B S hS c).map (definingIdealSheaf B S hS X Z).ι =
      (definingIdealSheaf B S hS W W₀).ι ≫
        (modulePullbackAdjunction B S hS c).homEquiv _ _
          (structureModulePullbackMap B S hS c) :=
    ((modulePullbackAdjunction B S hS c).homEquiv_naturality_right
      (idealSheafMap B S hS Z W₀ c f hsq) (definingIdealSheaf B S hS X Z).ι).symm.trans
      ((congrArg ((modulePullbackAdjunction B S hS c).homEquiv _ _)
        (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z W₀ c f hsq)).trans
        ((modulePullbackAdjunction B S hS c).homEquiv_naturality_left
          (definingIdealSheaf B S hS W W₀).ι (structureModulePullbackMap B S hS c)))
  exact (SheafOfModules.hom_congr_app_apply key V s).trans
    (congrArg (fun m => m.hom.app V ((definingIdealSheaf B S hS W W₀).ι.val.app V s))
      (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS c))

/-- **The comorphism read through the thickening, on a section of the ideal of `W₀`, through
the transposed map of ideal sheaves.** -/
theorem pushforward_map_conormalSetInclusion_app_conormalTranspose
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ⊚ c)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V
      (((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq) ≫
          (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS
            (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).val.app V s) =
      ((sheafCompose (SmallEtale.topology B S hS W.1) (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickening B S hS Z c)).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) :=
  (pushforward_map_app_val_app_comp_transpose B S hS (subspaceInclusion B S hS X Z) c
    (definingIdealSheaf B S hS X Z).toSheafOfModules
    (definingIdealSheaf B S hS W W₀).toSheafOfModules
    ((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq))
    (definingIdealSheaf B S hS W W₀).ι (definingIdealSheaf B S hS X Z).ι
    (firstOrderConormalSetInclusion B S hS Z hZ)
    (unit_comp_pushforward_map_conormalSetInclusion B S hS Z hZ)
    (modulePushforward_map_ι_homEquiv_idealSheafMap_val_app B S hS Z W₀ c f hsq) V s).trans
  (congrArg (fun m => m.hom.app V ((definingIdealSheaf B S hS W W₀).ι.val.app V s))
    (sheafCompose_map_structureSharpThroughThickening B S hS Z c)).symm

/-- The comorphism read in the direct image along `f ≫ j`, with that composite respelled in
`AlgebraicGeometry.AlgebraicSpaces`. -/
private theorem structureSharpThroughThickeningAt_comp_eq
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀) :
    structureSharpThroughThickeningAt B S hS Z c (f ≫ subspaceInclusion B S hS W W₀) hsq =
      structureSharpThroughThickeningAt B S hS Z c (f ⊚ subspaceInclusion B S hS W W₀)
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm :=
  rfl

/-- `AlgebraicGeometry.Space.structureSharpThroughThickeningAt` on sections. -/
private theorem structureSharpThroughThickeningAt_app_eq_eqToHom (e :
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : (subspaceInclusion B S hS X Z ⊚ c) = e) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x : ToType ((structureRingSheaf B S hS W).obj.obj V)) :
    (structureSharpThroughThickeningAt B S hS Z c e h).hom.app V x =
      (eqToHom (congrArg (fun m => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS W.1) (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) h)).hom.app V
        ((structureSharpThroughThickening B S hS Z c).hom.app V x) :=
  rfl

/-- `AlgebraicGeometry.Space.eqToHom_app_pushforward_map_eq` at the inclusion of the conormal
module. -/
private theorem eqToHom_app_pushforward_map_conormalSetInclusion
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (p : (subspaceInclusion B S hS X Z ⊚ c) = (f ⊚ subspaceInclusion B S hS W W₀))
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (x : ((modulePushforward B S hS (subspaceInclusion B S hS X Z ⊚ c)).obj
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).val.obj V) :
    (eqToHom (congrArg (fun m => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS W.1) (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) p)).hom.app V
      (((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ⊚ c)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V x) =
      ((smallToposMorphismTypeU B S hS (f ⊚ subspaceInclusion B S hS W W₀)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V
        ((eqToHom (congrArg (fun e => (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)) p)).val.app V x) :=
  eqToHom_app_pushforward_map_eq B S hS (subspaceInclusion B S hS X Z)
    p _ (firstOrderConormalSetInclusion B S hS Z hZ) V x

/-- The comorphism read through the thickening, on a section of the ideal of `W₀`, as a
morphism of sheaves of rings. -/
private theorem structureSharpThroughThickening_app_definingIdealSheaf_ι
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickening B S hS Z c).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ⊚ c)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V
          (((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq) ≫
          (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS
            (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).val.app V s) :=
  ((pushforward_map_conormalSetInclusion_app_conormalTranspose B S hS Z W₀ c f hZ hsq V s).trans
        (sheafCompose_forget_map_hom_app B S hS _ V _)).symm

/-- The same, transported along the square. -/
private theorem eqToHom_app_structureSharpThroughThickening_app_definingIdealSheaf_ι
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (eqToHom (congrArg (fun m => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS W.1) (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm)).hom.app V
      ((structureSharpThroughThickening B S hS Z c).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s)) =
      ((smallToposMorphismTypeU B S hS (f ⊚ subspaceInclusion B S hS W W₀)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V
        ((eqToHom (congrArg (fun e => (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules))
            (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f
              hsq).symm.symm)).val.app V
          (((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq) ≫
          (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS
            (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).val.app V s)) :=
    ((congrArg (fun y => (eqToHom (congrArg (fun m => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS W.1) (smallToposMorphismTypeU B S hS m).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm)).hom.app V
          y)
      (structureSharpThroughThickening_app_definingIdealSheaf_ι B S hS Z W₀ c f hZ hsq V s)).trans
    (eqToHom_app_pushforward_map_conormalSetInclusion B S hS Z W₀ c f hZ
      (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm V _))

/-- **The comorphism of `c` read through the thickening, on a section of the ideal of `W₀`, is
computed by the conormal map.**  Its value at a section `s` of the defining ideal sheaf of `W₀`
is the double transpose of the conormal map of the square, transported along the square and
applied to `s`, followed by the inclusion
`AlgebraicGeometry.Space.firstOrderConormalSetInclusion` of the conormal module.  Only the
conormal map depends on `c`. -/
theorem structureSharpThroughThickeningAt_app_definingIdealSheaf_ι
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c (f ⊚ subspaceInclusion B S hS W W₀)
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
      ((smallToposMorphismTypeU B S hS (f ⊚ subspaceInclusion B S hS W W₀)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V
        ((eqToHom (congrArg (fun e => (modulePushforward B S hS e).obj
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules))
            (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f
              hsq).symm.symm)).val.app V
          (((modulePullbackAdjunction B S hS c).homEquiv _ _ (idealSheafMap B S hS Z W₀ c f hsq) ≫
          (modulePushforward B S hS c).map ((modulePullbackAdjunction B S hS
            (subspaceInclusion B S hS X Z)).unit.app
              (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
          (modulePushforwardCompIso B S hS (subspaceInclusion B S hS X Z) c).hom.app
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).val.app V s)) :=
  (structureSharpThroughThickeningAt_app_eq_eqToHom B S hS Z c _
    (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm
      V _).trans
    (eqToHom_app_structureSharpThroughThickening_app_definingIdealSheaf_ι B S hS Z W₀ c f hZ hsq
      V s)

/-! ### Equal conormal maps -/

/-- Equal conormal maps give equal comorphisms on the sections of the defining ideal sheaf. -/
private theorem structureSharpThroughThickeningAt_app_ι_eq_of_conormalMap_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1) (c' : X ⟶ W)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (hsq' : subspaceInclusion B S hS X Z ≫ c' = f ≫ subspaceInclusion B S hS W W₀)
    (hC : conormalMap B S hS Z W₀ c f hsq = conormalMap B S hS Z W₀ c' f hsq')
    (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (definingIdealSheaf B S hS W W₀).toSheafOfModules.val.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c (f ⊚ subspaceInclusion B S hS W W₀)
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c f hsq).symm.symm).hom.app V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) =
    (structureSharpThroughThickeningAt B S hS Z c' (f ⊚ subspaceInclusion B S hS W W₀)
        (subspaceInclusion_comp_eq_comp_subspaceInclusion B S hS Z W₀ c' f hsq').symm.symm).hom.app
          V
        ((definingIdealSheaf B S hS W W₀).ι.val.app V s) := by
  have e := homEquiv_homEquiv_conormalMap B S hS Z W₀ c f hsq
  rw [hC] at e
  have ee := e.symm.trans (homEquiv_homEquiv_conormalMap B S hS Z W₀ c' f hsq')
  refine (structureSharpThroughThickeningAt_app_definingIdealSheaf_ι B S hS Z W₀ c f hZ hsq V
    s).trans ?_
  refine Eq.trans ?_
    (structureSharpThroughThickeningAt_app_definingIdealSheaf_ι B S hS Z W₀ c' f hZ hsq' V s).symm
  refine congrArg (fun y => ((smallToposMorphismTypeU B S hS
      (f ⊚ subspaceInclusion B S hS W W₀)).pushforward.map
        (firstOrderConormalSetInclusion B S hS Z hZ)).hom.app V y) ?_
  exact (comp_val_app_modules B S hS _ _ V s).symm.trans
    ((congrArg (fun m => m.val.app V s) ee).trans (comp_val_app_modules B S hS _ _ V s))

/-- The inclusion of the defining ideal sheaf on a section given by a function and its
membership. -/
private theorem definingIdealSheaf_ι_val_app_mk (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (a : ToType ((structureRingSheaf B S hS W).obj.obj V))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS W W₀)).hom.app V a = 0) :
    (definingIdealSheaf B S hS W W₀).ι.val.app V
      ⟨a, (mem_definingIdealAt_iff B S hS W W₀ V a).2 ha⟩ = a :=
  rfl

/-- **Equal conormal maps give comorphisms which agree on the ideal of `W₀`.**  For two morphisms
`c, c' : X ⟶ W` restricting to `f ≫ j` on the first-order thickening `Z ⊆ X`, whose canonical
maps of conormal modules of [Stacks Project, Tag 04CP] are equal, the two comorphisms read in
the direct image along `f ≫ j` agree on every local section of `𝒪_W` vanishing on `W₀`. -/
theorem structureSharpThroughThickeningAt_app_eq_of_conormalMap_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (c' : X ⟶ W)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (hsq' : subspaceInclusion B S hS X Z ≫ c' = f ≫ subspaceInclusion B S hS W W₀)
    (hC : conormalMap B S hS Z W₀ c f hsq = conormalMap B S hS Z W₀ c' f hsq')
    (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : ToType ((structureRingSheaf B S hS W).obj.obj V))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS W W₀)).hom.app V a = 0) :
    (structureSharpThroughThickeningAt B S hS Z c (f ≫ subspaceInclusion B S hS W W₀) hsq).hom.app
        V a =
    (structureSharpThroughThickeningAt B S hS Z c' (f ≫ subspaceInclusion B S hS W W₀)
        hsq').hom.app V a := by
  have h1 := structureSharpThroughThickeningAt_app_ι_eq_of_conormalMap_eq B S hS Z W₀ c f hZ c' hsq
    hsq' hC V
    ⟨a, (mem_definingIdealAt_iff B S hS W W₀ V a).2 ha⟩
  rw [definingIdealSheaf_ι_val_app_mk B S hS W₀ V a ha] at h1
  exact (congrArg (fun m => m.hom.app V a)
    (structureSharpThroughThickeningAt_comp_eq B S hS Z W₀ c f hsq)).trans
    (h1.trans (congrArg (fun m => m.hom.app V a)
      (structureSharpThroughThickeningAt_comp_eq B S hS Z W₀ c' f hsq')).symm)

/-- `AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening` on
sections. -/
private theorem ringUnit_comp_map_restrictedSharpThroughThickening_hom_app
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : ToType ((structureRingSheaf B S hS W).obj.obj V)) :
    (thickeningRingUnit B S hS W₀ ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (restrictedSharpThroughThickening B S hS Z W₀ c f hsq)).hom.app V a =
      (pushforwardRingSheafCompInv B S hS f (subspaceInclusion B S hS W W₀)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom.app V
        ((structureSharpThroughThickeningAt B S hS Z c
          (f ≫ subspaceInclusion B S hS W W₀) hsq).hom.app V a) :=
  ringSheafHom_congr_app_apply
    (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c f hsq) V a

/-- **Hypothesis (2) of [Stacks Project, Tag 0618] for the transported comorphisms.**  If the
two morphisms have equal conormal maps and `W₀ ⊆ W` is a first-order thickening, their
comorphisms transported to the small étale site of `W₀` agree on the sections killed by
`j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`.  This is the field `app_eq_of_app_eq_zero` of
`AlgebraicGeometry.Space.restrictedLiftDifferenceData`. -/
theorem restrictedSharpThroughThickening_app_eq_of_conormalMap_eq
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hW₀ : IsFirstOrderThickening B S hS W W₀.1) (c' : X ⟶ W)
    (hsq : subspaceInclusion B S hS X Z ≫ c = f ≫ subspaceInclusion B S hS W W₀)
    (hsq' : subspaceInclusion B S hS X Z ≫ c' = f ≫ subspaceInclusion B S hS W W₀)
    (hC : conormalMap B S hS Z W₀ c f hsq = conormalMap B S hS Z W₀ c' f hsq')
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType ((structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V))
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z W₀ c f hsq).hom.app V x =
      (restrictedSharpThroughThickening B S hS Z W₀ c' f hsq').hom.app V x :=
  app_eq_of_app_eq_zero_of_app_thickeningRingUnit_eq B S hS W₀ hW₀ _ _
    (fun V' a ha =>
      (ringUnit_comp_map_restrictedSharpThroughThickening_hom_app B S hS Z W₀ c f hsq V' a).trans
        ((congrArg ((pushforwardRingSheafCompInv B S hS f (subspaceInclusion B S hS W W₀)
              (structureRingSheafInverseImage B S hS
                (subspaceInclusion B S hS X Z))).hom.app V')
            (structureSharpThroughThickeningAt_app_eq_of_conormalMap_eq B S hS Z W₀ c f hZ c' hsq
              hsq' hC
              V' a ha)).trans
          (ringUnit_comp_map_restrictedSharpThroughThickening_hom_app B S hS Z W₀ c' f hsq'
            V' a).symm))
    V x hx

end AlgebraicGeometry.Space

end
