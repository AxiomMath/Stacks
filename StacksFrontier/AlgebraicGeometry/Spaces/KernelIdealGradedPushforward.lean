module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforwardNaturalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnital
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackUnitalCounit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraHomUnital

/-!
# The canonical map of conormal algebras of a commutative square

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
so `i ≫ g = f ≫ i'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X` and `𝓙 = Ker((f ≫ i')^♯) ⊆ 𝒪_{X'}` for the
kernel ideal sheaves of `i` and of the diagonal.  [Stacks Project, Tag 09RS] asserts a canonical
homomorphism of sheaves of graded `𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`.

`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` assembles it out of a
homomorphism of sheaves of graded `𝒪_X`-algebras `Ψ : g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` on the ambient space,
taken there as a parameter.  This file constructs that homomorphism, so the canonical map of
Stacks 09RS is available with no input beyond the square.

## The construction

The step of the source's proof that produces `Ψ` is that `g^♯ : g^{-1}𝒪_{X'} ⟶ 𝒪_X` carries
`g^{-1}𝓙` into `𝓘`, hence `g^{-1}(𝓙ⁿ)` into `𝓘ⁿ` for every `n`.  Read through the adjunction
`g^* ⊣ g_*` of sheaves of graded algebras of Stacks 0FQX, part (3), a homomorphism
`g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` is the same thing as a homomorphism `⨁ 𝓙ⁿ ⟶ g_*(⨁ 𝓘ⁿ)` of sheaves of graded
`𝒪_{X'}`-algebras on `X'`, and this is what is built:

* its degree-`n` component `𝓙ⁿ ⟶ g_*(𝓘ⁿ)` is the transpose, along the chartwise universal
  property of the direct image of Stacks 03LU, of pullback of regular functions along the
  vertical morphisms of the chart diagrams over `g`, which carries `𝓙ⁿ` into `𝓘ⁿ` by
  `AlgebraicGeometry.Space.mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback`;
* it is multiplicative because sections of a direct image are determined by their chart
  projections (`AlgebraicGeometry.Space.moduleChartProjection_ext`), and the chart projections,
  being natural in the sheaf of sets, carry the multiplication of a direct-image graded algebra
  to the multiplication of the source algebra
  (`Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_mul`).  On the chart projections
  the component is pullback of regular functions, which is a homomorphism of rings.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafZPowFMapOfEq`: the chartwise map `𝓙ⁿ ⟶ 𝓘ⁿ` of
  sections along `g`, for any spelling `j` of the composite `i ≫ g`.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap`: its transpose
  `𝓙ⁿ ⟶ g_*(𝓘ⁿ)`, a morphism of `𝒪_{X'}`-modules.
* `AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom`: the homomorphism
  `⨁ 𝓙ⁿ ⟶ g_*(⨁ 𝓘ⁿ)` of sheaves of graded `𝒪_{X'}`-algebras.
* `AlgebraicGeometry.Space.kernelIdealGradedPullbackHom`: its transpose
  `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ`, a homomorphism of sheaves of graded `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.conormalAlgebraSquareMap`: **the canonical map
  `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS].**
* `AlgebraicGeometry.Space.conormalAlgebraSquareUnitalHom`: the same map as a unital
  homomorphism of sheaves of graded algebras.

## Main results

* `AlgebraicGeometry.Space.moduleChartProjection_kernelIdealSheafZPowPushforwardMap`: the chart
  projections of the degree-`n` component are pullback of regular functions.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap_map_mul`: the degreewise components
  preserve products of homogeneous local sections.
* `AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom_map_one`,
  `AlgebraicGeometry.Space.kernelIdealGradedPullbackHom_map_one`,
  `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap_map_one` and
  `AlgebraicGeometry.Space.conormalAlgebraSquareMap_map_one`: every map above preserves the unit,
  so the canonical map is a homomorphism of graded algebras in the unital sense of the source.
* `AlgebraicGeometry.Space.conormalAlgebraSquareMap_eq`: the canonical map is the first factor
  `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap` followed by the ambient factor
  `AlgebraicGeometry.Space.conormalAlgebraAmbientSquareMapOfPullbackHom` at the homomorphism
  constructed here.

## Implementation notes

**Why the composite is a parameter `j` with `i ≫ g = j`.**  The canonical map of a square is
assembled in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMap.lean` with the
diagonal spelled `f ≫ i'`, so that its two factors compose with no cast between conormal
algebras; the ambient homomorphism is therefore needed with source the graded algebra of the
powers of `Ker((f ≫ i')^♯)`, not of `Ker((i ≫ g)^♯)`.  Taking the composite as a parameter puts
the square only into membership proofs, so no data is transported along it, and
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMapOfEq_rfl` records that at the reflexivity proof
the chartwise map is the existing `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`.

**Why the statement is for arbitrary morphisms and not for immersions.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMap.lean`, nothing below uses any
property of `i` or `i'`, so the statement is more general than Stacks 09RS, which takes both
vertical arrows to be immersions.  For an immersion Stacks 09RN takes the conormal algebra of the
closed factorisation through the complement of the boundary,
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`, which is isomorphic to but not the same
object as `AlgebraicGeometry.Space.conormalAlgebra`; the canonical map on those conormal algebras
is `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap` in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraOfImmersionSquareMap.lean`.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj
  pushforwardGradedAlgebra)

universe u

namespace SheafOfModules.GradedAlgebra

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Composition of homomorphisms of sheaves of graded algebras, read on a local section in
degree zero. -/
theorem comp_app_zero_apply {A₁ A₂ A₃ : GradedAlgebra.{u, u} R} (φ : A₁ ⟶ A₂) (ψ : A₂ ⟶ A₃)
    (U : Cᵒᵖ) (x : (A₁.piece 0).val.obj U) :
    ((φ ≫ ψ).app 0).val.app U x = (ψ.app 0).val.app U ((φ.app 0).val.app U x) :=
  rfl

/-- A composite of homomorphisms of sheaves of graded algebras preserving the unit over `U`
preserves the unit over `U`. -/
theorem comp_map_one {A₁ A₂ A₃ : GradedAlgebra.{u, u} R} (φ : A₁ ⟶ A₂) (ψ : A₂ ⟶ A₃)
    (U : Cᵒᵖ) (hφ : (φ.app 0).val.app U (A₁.one.eval U) = A₂.one.eval U)
    (hψ : (ψ.app 0).val.app U (A₂.one.eval U) = A₃.one.eval U) :
    ((φ ≫ ψ).app 0).val.app U (A₁.one.eval U) = A₃.one.eval U :=
  (congrArg (fun t => (ψ.app 0).val.app U t) hφ).trans hψ

/-- An isomorphism of sheaves of graded algebras preserves the unit. -/
theorem iso_hom_map_one {A₁ A₂ : GradedAlgebra.{u, u} R} (e : A₁ ≅ A₂) (U : Cᵒᵖ) :
    (e.hom.app 0).val.app U (A₁.one.eval U) = A₂.one.eval U :=
  have : IsIso (e.hom.app 0) :=
    ⟨⟨e.inv.app 0,
      by rw [← categoryStruct_comp_app, e.hom_inv_id, categoryStruct_id_app],
      by rw [← categoryStruct_comp_app, e.inv_hom_id, categoryStruct_id_app]⟩⟩
  Hom.map_one_of_isIso e.hom U

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' Z' : AlgebraicSpaces B S hS}

/-! ### The degreewise maps into the direct image -/

/-- **Pullback along a chart diagram over `g` carries `Ker(j^♯)ⁿ` into `Ker(i^♯)ⁿ`, for any
spelling `j` of the composite `i ≫ g`.**  This is
`AlgebraicGeometry.Space.mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback` with the
composite taken as a parameter. -/
theorem mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback_of_eq (i : Z ⟶ X)
    (g : X ⟶ X') (j : Z ⟶ X') (hj : i ≫ g = j) (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (n : ℤ) {s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V))}
    (hs : s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafZPow (kernelIdealSheaf B S hS j) n) (op d.V)) :
    (chartDiagramPullback B S hS g d).hom s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafZPow (kernelIdealSheaf B S hS i) n) (op d.U) := by
  subst hj
  exact mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback B S hS i g d n hs

/-- **The chartwise linear map of sections `𝓙ⁿ ⟶ 𝓘ⁿ` along `g`, for any spelling `j` of the
composite `i ≫ g`.**  On a commutative diagram of étale scheme charts over `g` it is pullback of
regular functions along the vertical morphism, corestricted to the `n`-th powers of the kernel
ideal sheaves `𝓙 = Ker(j^♯)` and `𝓘 = Ker(i^♯)`.

This is `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap` with the composite taken as a
parameter; the equation `i ≫ g = j` is used only in the proof that the corestriction is well
defined. -/
noncomputable def kernelIdealSheafZPowFMapOfEq (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (n : ℤ) :
    ModuleFMap B S hS g (kernelIdealSheafZPow B S hS i n).toSheafOfModules
      (kernelIdealSheafZPow B S hS j n).toSheafOfModules where
  app d s := ⟨(chartDiagramPullback B S hS g d).hom s.1,
    mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback_of_eq B S hS i g j hj d n s.2⟩
  naturality d d' k l hkl s := by
    have hcc : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X'.1).map l)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d'.g).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map k)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hkl]
    exact Subtype.ext (ConcreteCategory.congr_hom hcc s.1)
  map_add d s t := Subtype.ext (map_add (chartDiagramPullback B S hS g d).hom s.1 t.1)
  map_smul d r s := Subtype.ext (map_mul (chartDiagramPullback B S hS g d).hom r s.1)

/-- At the composite spelled `i ≫ g` and the reflexivity proof, the chartwise map is
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`. -/
theorem kernelIdealSheafZPowFMapOfEq_rfl (i : Z ⟶ X) (g : X ⟶ X') (n : ℤ) :
    kernelIdealSheafZPowFMapOfEq B S hS i g (i ≫ g) rfl n =
      kernelIdealSheafZPowFMap B S hS i g n :=
  rfl

/-- **The map `𝓙ⁿ ⟶ g_*(𝓘ⁿ)` of `𝒪_{X'}`-modules**: the transpose of
`AlgebraicGeometry.Space.kernelIdealSheafZPowFMapOfEq` along the chartwise universal property of
the direct image of Stacks 03LU, read in the direct image of modules of the morphism of small
étale ringed topoi of Stacks 03G8, which is the degree-`n` piece of the direct image of sheaves
of graded algebras. -/
noncomputable def kernelIdealSheafZPowPushforwardMap (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (n : ℤ) :
    (kernelIdealSheafZPow B S hS j n).toSheafOfModules ⟶
      (smallEtaleRingedToposHom B S hS g).pushforwardModules.obj
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules :=
  (modulePushforwardHomEquiv B S hS g _ _).symm (kernelIdealSheafZPowFMapOfEq B S hS i g j hj n) ≫
    (pushforwardModulesIsoModulePushforward B S hS g).inv.app _

/-- **The chart projections of `AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap` are
pullback of regular functions**: at the chart of `X` above `X ×_{X'} V` named by a structured
arrow, the image of a section of `𝓙ⁿ` over `V` projects to its pullback along the induced
morphism of charts. -/
theorem moduleChartProjection_kernelIdealSheafZPowPushforwardMap (i : Z ⟶ X) (g : X ⟶ X')
    (j : Z ⟶ X') (hj : i ≫ g = j) (n : ℤ) (V : SmallEtale B S hS X'.1)
    (a : StructuredArrow (op (chartBaseChange B S hS g V)) (comparisonFunctor B S hS X).op)
    (s : (kernelIdealSheafZPow B S hS j n).toSheafOfModules.val.obj (op V)) :
    (moduleChartProjection B S hS g V a).app
        (moduleSetSheaf B S hS X (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
        ((kernelIdealSheafZPowPushforwardMap B S hS i g j hj n).val.app (op V) s) =
      (kernelIdealSheafZPowFMapOfEq B S hS i g j hj n).app
        (chartDiagramOfIndex B S hS g V a) s :=
  moduleChartProjection_app_moduleFMapSection B S hS g _ _ _ V a s

/-- The chart projections of a direct image of sheaves of sets are natural in the sheaf. -/
theorem moduleChartProjection_app_map (g : X ⟶ X') (V : SmallEtale B S hS X'.1)
    (a : StructuredArrow (op (chartBaseChange B S hS g V)) (comparisonFunctor B S hS X).op)
    {F F' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (h : F ⟶ F')
    (x : ((smallEtaleDirectImage B S hS g).obj F).obj.obj (op V)) :
    (moduleChartProjection B S hS g V a).app F'
        (((smallEtaleDirectImage B S hS g).map h).hom.app (op V) x) =
      h.hom.app a.right ((moduleChartProjection B S hS g V a).app F x) := by
  have h := ConcreteCategory.congr_hom ((moduleChartProjection B S hS g V a).naturality h) x
  exact h

/-- A section of the direct image equals the image of a section of `𝓙ⁿ` as soon as the chart
projections agree with the chartwise map. -/
private theorem kernelIdealSheafZPowPushforwardMap_apply_eq (i : Z ⟶ X) (g : X ⟶ X')
    (j : Z ⟶ X') (hj : i ≫ g = j) (n : ℤ) (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x : (kernelIdealSheafZPow B S hS j n).toSheafOfModules.val.obj U)
    (y : ((smallEtaleRingedToposHom B S hS g).pushforwardModules.obj
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules).val.obj U)
    (h : ∀ c, (kernelIdealSheafZPowFMapOfEq B S hS i g j hj n).app
        (chartDiagramOfIndex B S hS g U.unop c) x =
      (moduleChartProjection B S hS g U.unop c).app
        (moduleSetSheaf B S hS X (kernelIdealSheafZPow B S hS i n).toSheafOfModules) y) :
    (kernelIdealSheafZPowPushforwardMap B S hS i g j hj n).val.app U x = y :=
  moduleChartProjection_ext B S hS g U.unop
    (moduleSetSheaf B S hS X (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
    fun c => (moduleChartProjection_kernelIdealSheafZPowPushforwardMap B S hS i g j hj n
      U.unop c x).trans (h c)

/-- **The degreewise maps `𝓙ⁿ ⟶ g_*(𝓘ⁿ)` preserve products of homogeneous local sections**, the
multiplication on the right being that of the direct image of the sheaf of graded algebras
`⨁ 𝓘ⁿ`.

Two sections of the direct image agree as soon as their chart projections do.  The chart
projections are natural in the sheaf of sets, so by
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_mul` they carry the multiplication
of the direct image to the multiplication of `⨁ 𝓘ⁿ`, which is multiplication of sections of
`𝒪_X`; and on the chart projections the degreewise maps are pullback of regular functions, a
homomorphism of rings. -/
theorem kernelIdealSheafZPowPushforwardMap_map_mul (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (a b : ℤ) (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x : (kernelIdealGradedAlgebra B S hS j).piece a |>.val.obj U)
    (y : (kernelIdealGradedAlgebra B S hS j).piece b |>.val.obj U) :
    (kernelIdealSheafZPowPushforwardMap B S hS i g j hj (a + b)).val.app U
        (((kernelIdealGradedAlgebra B S hS j).mul a b).app U x y) =
      ((pushforwardGradedAlgebra (smallEtaleRingedToposHom B S hS g)
          (kernelIdealGradedAlgebra B S hS i)).mul a b).app U
        ((kernelIdealSheafZPowPushforwardMap B S hS i g j hj a).val.app U x)
        ((kernelIdealSheafZPowPushforwardMap B S hS i g j hj b).val.app U y) := by
  refine kernelIdealSheafZPowPushforwardMap_apply_eq B S hS i g j hj (a + b) U _ _ fun c => ?_
  have key := Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_mul
    (smallEtaleRingedToposHom B S hS g) U c.right
    (fun F => (moduleChartProjection B S hS g U.unop c).app F)
    (fun h x => moduleChartProjection_app_map B S hS g U.unop c h x)
    (kernelIdealGradedAlgebra B S hS i) a b
    ((kernelIdealSheafZPowPushforwardMap B S hS i g j hj a).val.app U x)
    ((kernelIdealSheafZPowPushforwardMap B S hS i g j hj b).val.app U y)
  refine Eq.trans ?_ key.symm
  have hx := moduleChartProjection_kernelIdealSheafZPowPushforwardMap B S hS i g j hj a
    U.unop c x
  have hy := moduleChartProjection_kernelIdealSheafZPowPushforwardMap B S hS i g j hj b
    U.unop c y
  refine Eq.trans ?_ (congrArg₂ (fun p q => ((kernelIdealGradedAlgebra B S hS i).mul a b).app
    c.right p q) hx.symm hy.symm)
  exact SheafOfModules.reesPiece_ext (kernelIdealSheaf B S hS i)
    (map_mul (chartDiagramPullback B S hS g _).hom
      (SheafOfModules.reesVal _ x) (SheafOfModules.reesVal _ y))

/-! ### The homomorphisms of sheaves of graded algebras -/

/-- **The homomorphism `⨁ 𝓙ⁿ ⟶ g_*(⨁ 𝓘ⁿ)` of sheaves of graded `𝒪_{X'}`-algebras**, for
`𝓙 = Ker(j^♯)`, `𝓘 = Ker(i^♯)` and `j` a spelling of the composite `i ≫ g`.  Its degree-`n`
component is `AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap`, and it is
multiplicative by `AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap_map_mul`. -/
noncomputable def kernelIdealGradedPushforwardHom (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) :
    kernelIdealGradedAlgebra B S hS j ⟶
      (gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS g)).obj (kernelIdealGradedAlgebra B S hS i) where
  app n := kernelIdealSheafZPowPushforwardMap B S hS i g j hj n
  map_mul a b U x y := kernelIdealSheafZPowPushforwardMap_map_mul B S hS i g j hj a b U x y

/-- The degree-`n` component of `AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom` is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPushforwardMap`. -/
theorem kernelIdealGradedPushforwardHom_app (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (n : ℤ) :
    (kernelIdealGradedPushforwardHom B S hS i g j hj).app n =
      kernelIdealSheafZPowPushforwardMap B S hS i g j hj n :=
  rfl

/-- **The homomorphism `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` of sheaves of graded `𝒪_X`-algebras** on the ambient
space, for `𝓙 = Ker(j^♯)`, `𝓘 = Ker(i^♯)` and `j` a spelling of the composite `i ≫ g`: the
transpose of `AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom` along the adjunction
`g^* ⊣ g_*` of sheaves of graded algebras of Stacks 0FQX, part (3).

This is the map `g^{-1}(𝓙ⁿ) ⟶ 𝓘ⁿ` induced by `g^♯` in the proof of
[Stacks Project, Tag 09RS], as a homomorphism of sheaves of graded algebras. -/
noncomputable def kernelIdealGradedPullbackHom (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) :
    (gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS g)).obj (kernelIdealGradedAlgebra B S hS j) ⟶
      kernelIdealGradedAlgebra B S hS i :=
  ((gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
    (smallEtaleRingedToposHom B S hS g)).homEquiv _ _).symm
    (kernelIdealGradedPushforwardHom B S hS i g j hj)

/-- `AlgebraicGeometry.Space.kernelIdealGradedPullbackHom` transposes back to
`AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom`, which determines it. -/
theorem kernelIdealGradedPullbackHom_transpose (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) :
    ((gradedAdj (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
      (smallEtaleRingedToposHom B S hS g)).homEquiv _ _)
        (kernelIdealGradedPullbackHom B S hS i g j hj) =
      kernelIdealGradedPushforwardHom B S hS i g j hj :=
  Equiv.apply_symm_apply _ _

/-! ### The canonical map of Stacks 09RS -/

/-- **[Stacks Project, Tag 09RS]: the canonical map of conormal algebras of a commutative
square.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a commutative square of algebraic spaces over `S`, `hsq : i ≫ g = f ≫ i'`.  There is a
canonical homomorphism of sheaves of graded `𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`.

It is `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` at the ambient
homomorphism `AlgebraicGeometry.Space.kernelIdealGradedPullbackHom : g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` induced
by `g^♯`, where `𝓘 = Ker(i^♯)` and `𝓙 = Ker((f ≫ i')^♯)`: the first factor
`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*}` comes from the containment `Ker((i')^♯) ⊆ 𝓙`, and the second
factor `𝒞_{Z/X',*} ⟶ 𝒞_{Z/X,*}` is the inverse image along `i` of the ambient homomorphism, read
through the Stacks 03LU composition comparison `(f ≫ i')^* ≅ i^* g^*`.  This is the source's
proof: `g^♯` carries `g^{-1}((𝓘')ⁿ)` into `𝓘ⁿ`, and pulling back to `Z`, with
`i^{-1}g^{-1} = f^{-1}(i')^{-1}`, gives the map in each degree.

The statement takes `i` and `i'` to be arbitrary morphisms, where Stacks 09RS takes them to be
immersions; nothing here uses any property of them. -/
@[stacks 09RS "the canonical map f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} of graded algebras"]
noncomputable def conormalAlgebraSquareMap (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    (gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS Z')
        (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i') ⟶
      conormalAlgebra B S hS i :=
  conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq
    (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)

/-- The canonical map of Stacks 09RS is
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` at the ambient homomorphism
`AlgebraicGeometry.Space.kernelIdealGradedPullbackHom` induced by `g^♯`. -/
theorem conormalAlgebraSquareMap_eq_ofPullbackHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    conormalAlgebraSquareMap B S hS i i' f g hsq =
      conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq) :=
  rfl

/-- The canonical map of Stacks 09RS, unfolded: the first factor followed by the inverse image
along `i` of the ambient homomorphism, read through the composition comparison. -/
theorem conormalAlgebraSquareMap_eq_comp (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    conormalAlgebraSquareMap B S hS i i' f g hsq =
      conormalAlgebraPullbackCompMap B S hS f i' ≫
        gradedPullCompMapOfEq B S hS i g (f ≫ i') hsq.symm
          (kernelIdealGradedAlgebra B S hS (f ≫ i')) (kernelIdealGradedAlgebra B S hS i)
          (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq) :=
  rfl

/-- The canonical map of Stacks 09RS is the first factor followed by the ambient factor at the
ambient homomorphism induced by `g^♯`. -/
theorem conormalAlgebraSquareMap_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    conormalAlgebraSquareMap B S hS i i' f g hsq =
      conormalAlgebraPullbackCompMap B S hS f i' ≫
        conormalAlgebraAmbientSquareMapOfPullbackHom B S hS i i' f g hsq
          (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq) :=
  rfl

/-! ### The canonical map preserves the unit -/

/-- **The homomorphism `⨁ 𝓙ⁿ ⟶ g_*(⨁ 𝓘ⁿ)` preserves the unit.**  Its chart projections in
degree zero are pullback of regular functions, which carries `1` to `1`, and the chart
projections of the unit of a direct-image graded algebra are the unit of the source algebra by
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_one`. -/
theorem kernelIdealGradedPushforwardHom_map_one (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (U : (SmallEtale B S hS X'.1)ᵒᵖ) :
    ((kernelIdealGradedPushforwardHom B S hS i g j hj).app 0).val.app U
        ((kernelIdealGradedAlgebra B S hS j).one.eval U) =
      ((gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS g)).obj (kernelIdealGradedAlgebra B S hS i)).one.eval
        U := by
  refine kernelIdealSheafZPowPushforwardMap_apply_eq B S hS i g j hj 0 U _ _ fun c => ?_
  have key := Stacks.Sheaves.GradedAlgebraEssentiallySmall.natural_family_one
    (smallEtaleRingedToposHom B S hS g) U c.right
    (fun F => (moduleChartProjection B S hS g U.unop c).app F)
    (fun h x => moduleChartProjection_app_map B S hS g U.unop c h x)
    (kernelIdealGradedAlgebra B S hS i)
  refine Eq.trans ?_ key.symm
  exact SheafOfModules.reesPiece_ext (kernelIdealSheaf B S hS i)
    (map_one (chartDiagramPullback B S hS g _).hom)

/-- **The ambient homomorphism `g^*(⨁ 𝓙ⁿ) ⟶ ⨁ 𝓘ⁿ` preserves the unit.**  It is the pullback of
`AlgebraicGeometry.Space.kernelIdealGradedPushforwardHom`, which preserves the unit, followed by
the counit of the adjunction of Stacks 0FQX, part (3), which does too. -/
theorem kernelIdealGradedPullbackHom_map_one (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X')
    (hj : i ≫ g = j) (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    ((kernelIdealGradedPullbackHom B S hS i g j hj).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
            (kernelIdealGradedAlgebra B S hS j)).one.eval U) =
      (kernelIdealGradedAlgebra B S hS i).one.eval U := by
  have h := Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one
    (smallEtaleRingedToposHom B S hS g).toRingedToposModulesHom
    (kernelIdealGradedPushforwardHom B S hS i g j hj)
    (kernelIdealGradedPushforwardHom_map_one B S hS i g j hj) U
  refine (congrArg (fun t => (((gradedAdj (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).counit.app
      (kernelIdealGradedAlgebra B S hS i)).app 0).val.app U t) h).trans ?_
  exact Stacks.Sheaves.GradedAlgebraEssentiallySmall.counitApp_map_one
    (smallEtaleRingedToposHom B S hS g) (kernelIdealGradedAlgebra B S hS i) U

/-- **The first factor `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*}` preserves the unit.**  It is the inverse of
the composition comparison, an isomorphism, followed by the pullback of the inclusion
`⨁ (𝓘')ⁿ ⟶ ⨁ 𝓙ⁿ`, which preserves the unit `1`. -/
theorem conormalAlgebraPullbackCompMap_map_one (f : Z ⟶ Z') (i' : Z' ⟶ X')
    (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    ((conormalAlgebraPullbackCompMap B S hS f i').app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
          (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i')).one.eval U) =
      ((gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS (f ≫ i'))).obj
            (kernelIdealGradedAlgebra B S hS (f ≫ i'))).one.eval U :=
  SheafOfModules.GradedAlgebra.comp_map_one _ _ U
    (SheafOfModules.GradedAlgebra.iso_hom_map_one
      ((gradedAlgebraPullbackCompIso B S hS f i').app
      (kernelIdealGradedAlgebra B S hS i')).symm U)
    (Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one
      (smallEtaleRingedToposModulesHom B S hS (f ≫ i'))
      (kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl)
      (fun _ => SheafOfModules.reesPiece_ext _ rfl) U)

/-- The inverse image along `i` of a homomorphism out of an inverse image along `g`, with its
source rewritten as an inverse image along a spelling `j` of `i ≫ g`, preserves the unit as soon
as the homomorphism does: the composition comparison is an isomorphism, and pullback of sheaves
of graded algebras preserves unital homomorphisms. -/
theorem gradedPullCompMapOfEq_map_one (i : Z ⟶ X) (g : X ⟶ X') (j : Z ⟶ X') (hj : j = i ≫ g)
    (B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X'))
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj B' ⟶ A)
    (hΨ : ∀ V, (Ψ.app 0).val.app V
      (((gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
          B').one.eval V) = A.one.eval V)
    (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    ((gradedPullCompMapOfEq B S hS i g j hj B' A Ψ).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS j)).obj
            B').one.eval U) =
      ((gradedPull (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).obj
          A).one.eval U :=
  SheafOfModules.GradedAlgebra.comp_map_one _ _ U
    (SheafOfModules.GradedAlgebra.iso_hom_map_one
      ((gradedAlgebraPullbackCompIsoOfEq B S hS i g j hj).app B') U)
    (Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one
      (smallEtaleRingedToposHom B S hS i).toRingedToposModulesHom Ψ hΨ U)

/-- **The ambient factor `𝒞_{Z/X',*} ⟶ 𝒞_{Z/X,*}` of the canonical map preserves the unit**, at
the ambient homomorphism `AlgebraicGeometry.Space.kernelIdealGradedPullbackHom` induced by
`g^♯`.  The conormal algebras are spelled here as the inverse images of the graded algebras of
the powers of the kernel ideal sheaves, which they are by definition. -/
theorem gradedPullCompMapOfEq_kernelIdealGradedPullbackHom_map_one (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    ((gradedPullCompMapOfEq B S hS i g (f ≫ i') hsq.symm _ _
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS (f ≫ i'))).obj
            (kernelIdealGradedAlgebra B S hS (f ≫ i'))).one.eval U) =
      ((gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).obj
            (kernelIdealGradedAlgebra B S hS i)).one.eval U :=
  gradedPullCompMapOfEq_map_one B S hS i g (f ≫ i') hsq.symm _ _
    (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)
    (kernelIdealGradedPullbackHom_map_one B S hS i g (f ≫ i') hsq) U

/-- **[Stacks Project, Tag 09RS]: the canonical map of conormal algebras preserves the unit**,
so it is a homomorphism of sheaves of graded `𝒪_Z`-algebras in the unital sense of the source.
It is the first factor, which preserves the unit by
`AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap_map_one`, followed by the ambient factor,
which does by `AlgebraicGeometry.Space.gradedPullCompMapOfEq_kernelIdealGradedPullbackHom_map_one`:
the ambient homomorphism preserves the unit
(`AlgebraicGeometry.Space.kernelIdealGradedPullbackHom_map_one`), pullback of sheaves of graded
algebras preserves unital homomorphisms
(`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one`), and the
composition comparisons are isomorphisms. -/
theorem conormalAlgebraSquareMap_map_one (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (U : (SmallEtale B S hS Z.1)ᵒᵖ) :
    ((conormalAlgebraSquareMap B S hS i i' f g hsq).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
          (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i')).one.eval U) =
      (conormalAlgebra B S hS i).one.eval U := by
  refine (congrArg (fun m => (m.app 0).val.app U
    (((gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
          (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i')).one.eval U))
    (conormalAlgebraSquareMap_eq_comp B S hS i i' f g hsq)).trans ?_
  refine (SheafOfModules.GradedAlgebra.comp_app_zero_apply
    (conormalAlgebraPullbackCompMap B S hS f i')
    (gradedPullCompMapOfEq B S hS i g (f ≫ i') hsq.symm _ _
      (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)) U _).trans ?_
  refine (congrArg (fun t => ((gradedPullCompMapOfEq B S hS i g (f ≫ i') hsq.symm _ _
        (kernelIdealGradedPullbackHom B S hS i g (f ≫ i') hsq)).app 0).val.app U t)
    (conormalAlgebraPullbackCompMap_map_one B S hS f i' U)).trans ?_
  exact gradedPullCompMapOfEq_kernelIdealGradedPullbackHom_map_one B S hS i i' f g hsq U

/-- **[Stacks Project, Tag 09RS], as a unital homomorphism**: the canonical map
`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of `AlgebraicGeometry.Space.conormalAlgebraSquareMap` together with
its unit law `AlgebraicGeometry.Space.conormalAlgebraSquareMap_map_one`. -/
noncomputable def conormalAlgebraSquareUnitalHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    SheafOfModules.GradedAlgebra.UnitalHom
      ((gradedPull (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS Z')
        (smallEtaleRingedToposHom B S hS f)).obj (conormalAlgebra B S hS i'))
      (conormalAlgebra B S hS i) where
  app := (conormalAlgebraSquareMap B S hS i i' f g hsq).app
  map_mul := (conormalAlgebraSquareMap B S hS i i' f g hsq).map_mul
  map_one := conormalAlgebraSquareMap_map_one B S hS i i' f g hsq

/-- The underlying homomorphism of `AlgebraicGeometry.Space.conormalAlgebraSquareUnitalHom` is
the canonical map `AlgebraicGeometry.Space.conormalAlgebraSquareMap`. -/
theorem conormalAlgebraSquareUnitalHom_toHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    (conormalAlgebraSquareUnitalHom B S hS i i' f g hsq).toHom =
      conormalAlgebraSquareMap B S hS i i' f g hsq :=
  SheafOfModules.GradedAlgebra.Hom.ext fun _ => rfl

end AlgebraicGeometry.Space

end
