module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangle
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierNormalHomVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedDualAtTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf

/-!
# The triangulated comparison of Tag 0B4B

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`,
ideal sheaf `ℐ_D`, invertible sheaf `𝒪_X(D)` and normal sheaf `𝒩 = i^* 𝒪_X(D)`. The isomorphism
assertion of [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B) is, by
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_dualTriangleVertex`,
the assertion that

`Stacks.Divisors.normalShiftToDualTriangleVertex : Ri_*(𝒩[-1]) ⟶ R ℰom((i_* 𝒪_D)[0], 𝒪_X)`

is invertible, the target being the first vertex of the dual triangle of the ideal sequence
`Stacks.Divisors.exists_distinguished_derivedDual_divisorIdeal`, whose other two vertices are
`R ℰom(𝒪_X[0], 𝒪_X)` and `R ℰom(ℐ_D[0], 𝒪_X) ≅ 𝒪_X(D)[0]`
(`Stacks.Divisors.derivedDualIdealSheafIso`).

This file proves that assertion under the hypothesis `hmor₁` that, under the identification
`R ℰom(𝒪_X[0], 𝒪_X) ≅ 𝒪_X[0]`, the first morphism of the dual triangle is the derived evaluation at
one `Stacks.Divisors.derivedSheafHomEvaluationAtOne`, and expresses `hmor₁` as an identity of two
natural transformations `R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭`.

## Main definitions

* `Stacks.Divisors.pushforwardNormalShiftObj` and `Stacks.Divisors.pushforwardNormalShift`:
  `Ri_*(𝒩[-1])` and the morphism `ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X`, with their types spelled over
  `X.Modules`.
* `Stacks.Divisors.normalPushforwardShiftIso`: the identification
  `Ri_*(𝒩[-1]) ≅ ((i_* 𝒩)[0])⟦-1⟧`.
* `Stacks.Divisors.dualTriangleSecondVertexIso`: the identification
  `R ℰom(𝒪_X[0], 𝒪_X) ≅ 𝒪_X[0]` of the second vertex of the dual triangle, by the
  representation theorem of [Stacks, Tag 08JH] at the structure sheaf.
* `Stacks.Divisors.pushforwardStructureSheafDerivedUnit`: the unit `𝒪_X ⟶ i_* 𝒪_D` as a
  morphism `𝒪_X[0] ⟶ Ri_* 𝒪_D[0]` of `D(𝒪_X)`.
* `Stacks.Divisors.dualTriangleFirstNatTrans` and
  `Stacks.Divisors.derivedEvaluationAtOneNatTrans`: the two sides of `hmor₁` as natural
  transformations `R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭`.

## Main results

* `Stacks.Divisors.normalPushforwardShiftIso_hom_comp_invRotate_mor₁`: `ψ` is, up to sign, the
  first morphism of the inverse rotation of the triangle of the normal short exact sequence.
* `Stacks.Divisors.dualTriangleSecondVertexIso_hom_comp_normalMor₁`: the second morphism of the
  dual triangle is multiplication by the canonical section `1_D`, read through
  `Stacks.Divisors.dualTriangleSecondVertexIso` and `Stacks.Divisors.derivedDualIdealSheafIso`.
* `Stacks.Divisors.dualTriangleSecondVertexIso_hom_eq_derivedStructureSheafHomIso`: that
  identification of the second vertex is evaluation at the unit section.
* `Stacks.Divisors.dualTriangleFirstMap_of_natTrans_eq` and
  `Stacks.Divisors.dualTriangleFirstMap_of_natTrans_app`: `hmor₁` follows from the identity of
  the two natural transformations, or from their agreement at any object isomorphic to
  `𝒪_X[0]`.
* `Stacks.Divisors.derivedEvaluationAtOneNatTrans_eq_counit`: the second of those two
  transformations is the inverse of the bifunctor form of [Stacks, Tag 0A77] followed by the trace
  of [Stacks, Tag 0A76].
* `Stacks.Divisors.isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap` and
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`:
  the isomorphism assertion of [Stacks, Tag 0B4B] under `hmor₁`.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (StructureSheafModules derivedSheafHom ringedSite)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

/-- **A morphism between the first vertices of two distinguished triangles is invertible** if the
two squares it makes with isomorphisms `e₂`, `e₃` of the remaining vertices commute and every
morphism `T.obj₁⟦1⟧ ⟶ T'.obj₃` vanishes. -/
private theorem isIso_of_distTriang_of_forall_eq_zero {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
    [Pretriangulated C] {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a : T.obj₁ ⟶ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂) (e₃ : T.obj₃ ≅ T'.obj₃)
    (h₁ : T.mor₁ ≫ e₂.hom = a ≫ T'.mor₁)
    (h₂ : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
    (hvan : ∀ w : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, w = 0) :
    IsIso a := by
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism T T' hT hT' a e₂.hom h₁
  have hzero : T.mor₂ ≫ (c - e₃.hom) = 0 := by
    rw [Preadditive.comp_sub, hc₂, h₂, sub_self]
  obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ T hT (c - e₃.hom) hzero
  have hce : c = e₃.hom := sub_eq_zero.1 (by rw [hw, hvan w, comp_zero])
  have : IsIso c := by rw [hce]; infer_instance
  exact isIso₁_of_isIso₂₃ (T := T) (T' := T')
    { hom₁ := a, hom₂ := e₂.hom, hom₃ := c, comm₁ := h₁, comm₂ := hc₂, comm₃ := hc₃ }
    hT hT' inferInstance this

/-- A morphism that becomes zero after conjugating by two isomorphisms is zero. -/
private theorem eq_zero_of_iso_comp_comp_eq_zero {C : Type*} [Category C] [Preadditive C]
    {A A' B B' : C} (eA : A' ≅ A) (eB : B ≅ B') {f : A ⟶ B}
    (h : eA.hom ≫ f ≫ eB.hom = 0) : f = 0 := by
  simpa using congrArg (fun t ↦ eA.inv ≫ t ≫ eB.inv) h

/-- A morphism whose negative is invertible is invertible. -/
private theorem isIso_of_isIso_neg {C : Type*} [Category C] [Preadditive C] {A B : C}
    (f : A ⟶ B) (h : IsIso (-f)) : IsIso f :=
  ⟨-(inv (-f)), by rw [Preadditive.comp_neg, ← Preadditive.neg_comp, IsIso.hom_inv_id],
    by rw [Preadditive.neg_comp, ← Preadditive.comp_neg, IsIso.inv_hom_id]⟩

/-- The signed form of `Stacks.Divisors.isIso_of_distTriang_of_forall_eq_zero`: the square on the
first morphisms commutes up to sign. -/
private theorem isIso_of_distTriang_of_forall_eq_zero_neg {C : Type*} [Category C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a : T.obj₁ ⟶ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂) (e₃ : T.obj₃ ≅ T'.obj₃)
    (h₁ : T.mor₁ ≫ e₂.hom = -(a ≫ T'.mor₁))
    (h₂ : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
    (hvan : ∀ w : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃, w = 0) :
    IsIso a :=
  isIso_of_isIso_neg a
    (isIso_of_distTriang_of_forall_eq_zero hT hT' (-a) e₂ e₃
      (h₁.trans (Preadditive.neg_comp _ _).symm) h₂ hvan)

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- `Ri_*(𝒩[-1])`, the source of the comparison morphism of [Stacks, Tag 0B4B] pushed forward,
as an object of `D(𝒪_X)`. -/
def pushforwardNormalShiftObj : DerivedCategory X.Modules :=
  (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))

/-- The morphism `ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X` of `Stacks.Divisors`
`.pushforwardNormalShiftToStructureSheaf`, with its source and target written as the objects of
`D(𝒪_X)` that the triangle of the normal short exact sequence presents them as. -/
def pushforwardNormalShift :
    pushforwardNormalShiftObj D ⟶
      (normalShortComplex_shortExact D).singleTriangle.obj₁ :=
  pushforwardNormalShiftToStructureSheaf D

/-- Derived pushforward along the closed immersion of `D` identifies `Ri_*(𝒩[-1])` with the
shift by `-1` of `(i_* 𝒩)[0]`. -/
def normalPushforwardShiftIso :
    pushforwardNormalShiftObj D ≅
      ((normalShortComplex_shortExact D).singleTriangle.obj₃)⟦(-1 : ℤ)⟧ :=
  (modulePushforward (closedQuotient D).i).mapDerivedCategory.mapIso
      (((DerivedCategory.singleFunctors D.subscheme.Modules).shiftIso (-1) 1 0
        (by ring)).symm.app ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≪≫
    ((modulePushforward (closedQuotient D).i).mapDerivedCategory.commShiftIso (-1 : ℤ)).app
        ((DerivedCategory.singleFunctor D.subscheme.Modules 0).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).mapIso
        (((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))

/-- **The morphism `ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X` is the first morphism of the inverse rotation of the
triangle of the normal short exact sequence**, read through
`Stacks.Divisors.normalPushforwardShiftIso` and up to the sign that the inverse rotation
carries. -/
theorem normalPushforwardShiftIso_hom_comp_invRotate_mor₁ :
    (normalPushforwardShiftIso D).hom ≫
        (Triangle.invRotate (normalShortComplex_shortExact D).singleTriangle).mor₁ =
      -pushforwardNormalShift D := by
  change (normalPushforwardShiftIso D).hom ≫
      (-(((normalExtensionClass D)⟦(-1 : ℤ)⟧') ≫
        (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)))) = _
  refine (Preadditive.comp_neg _ _).trans (congrArg Neg.neg ?_)
  change ((modulePushforward (closedQuotient D).i).mapDerivedCategory.map
          (((DerivedCategory.singleFunctors D.subscheme.Modules).shiftIso (-1) 1 0
            (by ring)).inv.app
              ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≫
        (((modulePushforward (closedQuotient D).i).mapDerivedCategory.commShiftIso
              (-1 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor D.subscheme.Modules 0).obj
              ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≫
          ((((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).hom.app
            ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)))⟦(-1 : ℤ)⟧'))) ≫
      (((normalExtensionClass D)⟦(-1 : ℤ)⟧') ≫
        (shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1) (by ring)).hom.app
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))) = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t ↦ (modulePushforward (closedQuotient D).i).mapDerivedCategory.map
        (((DerivedCategory.singleFunctors D.subscheme.Modules).shiftIso (-1) 1 0
          (by ring)).inv.app
            ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ≫ t)
      (Category.assoc _ _ _))

/-- **The second vertex of the dual triangle of the ideal sequence is `𝒪_X`:**

`R ℰom(𝒪_X[0], 𝒪_X[0]) ≅ 𝒪_X[0]` in `D(𝒪_X)`.

The structure sheaf is invertible, so the derived internal Hom out of it in a single degree is
represented by the internal Hom complex
(`Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso`, which is [Stacks, Tag 08JH]
relaxed through [Stacks, Tag 0B8M]), and that complex is the dual sheaf `ℰom(𝒪_X, 𝒪_X)` placed
in degree zero, which is `𝒪_X` itself
(`Stacks.SheafOfModules.internalHomSheafUnitIso`). -/
def dualTriangleSecondVertexIso :
    ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).obj
        (op (divisorIdealShortComplex_shortExact D).singleTriangle.obj₂) ≅
      (normalShortComplex_shortExact D).singleTriangle.obj₁ :=
  haveI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (_root_.structureSheaf X.sheaf).property
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso X.sheaf
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ≪≫
    (DerivedCategory.singleFunctor X.Modules 0).mapIso
      (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)))

/-- The unit of the structure sheaf of a scheme is invertible. -/
private theorem isInvertible_unit_structureSheaf :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (_root_.structureSheaf X.sheaf).property
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- **The identification of the second vertex of the dual triangle is evaluation at the unit
section**, that is, the component at `𝒪_X[0]` of the natural identification
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso` of the derived internal Hom out of
the structure sheaf with the identity functor. -/
theorem dualTriangleSecondVertexIso_hom_eq_derivedStructureSheafHomIso :
    (dualTriangleSecondVertexIso D).hom =
      (RingedSite.derivedStructureSheafHomIso (ringedSite X.sheaf)
        (RingedSite.derivedStructureSheaf (ringedSite X.sheaf))).hom := by
  have := isInvertible_unit_structureSheaf (X := X)
  exact Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso_unit_eq X.sheaf

/-- **The unit `𝒪_X ⟶ i_* 𝒪_D` as a morphism `𝒪_X[0] ⟶ Ri_* 𝒪_D[0]` of `D(𝒪_X)`**: the second
morphism of the triangle of the ideal sequence, followed backwards by the identification of
`Ri_* 𝒪_D[0]` with `(i_* 𝒪_D)[0]` that
`Stacks.Divisors.derivedSheafHomPushforwardStructureSheafIsoDualVertex` reads in the
contravariant variable of the derived internal Hom. -/
def pushforwardStructureSheafDerivedUnit :
    (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X) ⟶
      (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf (ringedSite (closedQuotient D).Z.sheaf)) :=
  (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂ ≫
    (((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit
        (structureSheafRing D.subscheme.toRingedSpace))).inv

/-- **The dual triangle's first morphism as a natural transformation
`R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭`:** restriction along the unit `𝒪_X ⟶ i_* 𝒪_D`, followed by the
trivialisation `AlgebraicGeometry.RingedSite.derivedStructureSheafHomNatIso` of the derived
internal Hom out of the structure sheaf. -/
def dualTriangleFirstNatTrans :
    (derivedSheafHom X.sheaf).obj
        (op ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (ringedSite (closedQuotient D).Z.sheaf)))) ⟶
      𝟭 (DerivedCategory X.Modules) :=
  (derivedSheafHom X.sheaf).map (pushforwardStructureSheafDerivedUnit D).op ≫
    (RingedSite.derivedStructureSheafHomNatIso (ringedSite X.sheaf)).hom

/-- **The derived evaluation at one as a natural transformation `R ℰom(Ri_* 𝒪_D, -) ⟶ 𝟭`:** the
identification of the two models of [Stacks, Tag 0A77] followed by the derived evaluation at one
of [Stacks, Tag 0B6M]. -/
def derivedEvaluationAtOneNatTrans :
    (derivedSheafHom X.sheaf).obj
        (op ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (ringedSite (closedQuotient D).Z.sheaf)))) ⟶
      𝟭 (DerivedCategory X.Modules) :=
  (closedQuotient D).derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom.inv ≫
    (closedQuotient D).derivedEvaluationAtOne

omit [IsEffectiveCartierDivisor D] in
/-- **The derived evaluation at one, read in the bifunctor, is the trace of [Stacks, Tag 0A76]
carried across the bifunctor form of [Stacks, Tag 0A77]**: it is the inverse of
`derivedSheafHomExactSupportPushforwardNatIso` followed by the counit of the adjunction
`Ri_* ⊣ R ℰom(𝒪_D, -)`. -/
theorem derivedEvaluationAtOneNatTrans_eq_counit :
    derivedEvaluationAtOneNatTrans D =
      (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.inv ≫
        (closedQuotient D).derivedModulePushforwardSheafHomExactSupportAdjunction.counit :=
  (Category.assoc _ _ _).trans
    (congrArg
      (fun t : (closedQuotient D).derivedSheafHomExactSupport ⋙
          (modulePushforward (closedQuotient D).i).mapDerivedCategory ⟶ _ ↦
        (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.inv ≫ t)
      (closedQuotient
        D).derivedModulePushforwardDerivedSheafHomExactSupportIso_hom_comp_derivedEvaluationAtOne)

omit [IsEffectiveCartierDivisor D] in
/-- The component at `𝒪_X[0]` of `Stacks.Divisors.derivedEvaluationAtOneNatTrans` is the derived
evaluation at one `Stacks.Divisors.derivedSheafHomEvaluationAtOne`. -/
theorem derivedEvaluationAtOneNatTrans_app_structureSheaf :
    (derivedEvaluationAtOneNatTrans D).app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) =
      derivedSheafHomEvaluationAtOne D := rfl

/-- The component at `𝒪_X[0]` of `Stacks.Divisors.dualTriangleFirstNatTrans` is the dual triangle's
first morphism read through `Stacks.Divisors.dualTriangleSecondVertexIso`, precomposed with the
identification of the triangle's first vertex. -/
theorem dualTriangleFirstNatTrans_app_structureSheaf :
    (dualTriangleFirstNatTrans D).app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) =
      (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).hom ≫
        ((derivedSheafHom X.sheaf).flip.obj
              (DerivedCategory.Q.obj
                (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
            (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
          (dualTriangleSecondVertexIso D).hom := by
  rw [dualTriangleSecondVertexIso_hom_eq_derivedStructureSheafHomIso]
  change ((derivedSheafHom X.sheaf).map (pushforwardStructureSheafDerivedUnit D).op).app _ ≫
      (RingedSite.derivedStructureSheafHomIso (ringedSite X.sheaf)
        (RingedSite.derivedStructureSheaf (ringedSite X.sheaf))).hom = _
  have hmap := Functor.map_comp (derivedSheafHom X.sheaf)
    (((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit
        (structureSheafRing D.subscheme.toRingedSpace))).inv.op
    (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op
  refine Eq.trans (congrArg
    (fun f : ((derivedSheafHom X.sheaf).obj
        (op ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (ringedSite (closedQuotient D).Z.sheaf))))).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) ⟶ _ ↦
      f ≫ (RingedSite.derivedStructureSheafHomIso (ringedSite X.sheaf)
        (RingedSite.derivedStructureSheaf (ringedSite X.sheaf))).hom)
    (NatTrans.congr_app hmap
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)))) ?_
  exact Category.assoc _ _ _

/-- Two natural transformations into the identity functor which agree at one object agree at
every object isomorphic to it. -/
private theorem natTrans_app_eq_of_iso {C : Type*} [Category C] {F : C ⥤ C}
    {α β : F ⟶ 𝟭 C} {Z W : C} (e : Z ≅ W) (h : α.app Z = β.app Z) : α.app W = β.app W := by
  refine (cancel_epi (F.map e.hom)).mp ?_
  rw [α.naturality, β.naturality, h]

/-- **The first morphism of the dual triangle, read through
`Stacks.Divisors.dualTriangleSecondVertexIso`, is the derived evaluation at one** as soon as
`Stacks.Divisors.dualTriangleFirstNatTrans` and `Stacks.Divisors.derivedEvaluationAtOneNatTrans`
agree at some object isomorphic to `𝒪_X[0]`. -/
theorem dualTriangleFirstMap_of_natTrans_app
    (Z : DerivedCategory X.Modules)
    (e : Z ≅ (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))
    (h : (dualTriangleFirstNatTrans D).app Z = (derivedEvaluationAtOneNatTrans D).app Z) :
    ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
        (dualTriangleSecondVertexIso D).hom =
      (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
        derivedSheafHomEvaluationAtOne D :=
  (Iso.eq_inv_comp (derivedSheafHomPushforwardStructureSheafIsoDualVertex D)).mpr
    ((dualTriangleFirstNatTrans_app_structureSheaf D).symm.trans
      ((natTrans_app_eq_of_iso e h).trans
        (derivedEvaluationAtOneNatTrans_app_structureSheaf D)))

/-- **The first morphism of the dual triangle, read through
`Stacks.Divisors.dualTriangleSecondVertexIso`, is the derived evaluation at one** as soon as the
two natural transformations `Stacks.Divisors.dualTriangleFirstNatTrans` and
`Stacks.Divisors.derivedEvaluationAtOneNatTrans` are equal. -/
theorem dualTriangleFirstMap_of_natTrans_eq
    (h : dualTriangleFirstNatTrans D = derivedEvaluationAtOneNatTrans D) :
    ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
        (dualTriangleSecondVertexIso D).hom =
      (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
        derivedSheafHomEvaluationAtOne D :=
  dualTriangleFirstMap_of_natTrans_app D _ (Iso.refl _) (NatTrans.congr_app h _)

/-- If `e.hom ≫ m = -ps` and `al ≫ u ≫ b.hom = ps`, then `m ≫ b.inv = -((e.inv ≫ al) ≫ u)`. -/
private theorem square_one {C : Type*} [Category C] [Preadditive C] {P P' Q A B : C}
    (e : P ≅ P') (m : P' ⟶ Q) (ps : P ⟶ Q) (al : P ⟶ A) (u : A ⟶ B) (b : B ≅ Q)
    (hm : e.hom ≫ m = -ps) (hu : al ≫ u ≫ b.hom = ps) :
    m ≫ b.inv = -((e.inv ≫ al) ≫ u) := by
  have hm' : m = e.inv ≫ (-ps) := by rw [← hm, Iso.inv_hom_id_assoc]
  rw [hm', ← hu]
  simp [Category.assoc]

/-- If `b.hom ≫ n = v ≫ c.hom`, then `n ≫ c.inv = b.inv ≫ v`. -/
private theorem square_two {C : Type*} [Category C] {Q R B C' : C}
    (n : Q ⟶ R) (v : B ⟶ C') (b : B ≅ Q) (c : C' ≅ R)
    (h : b.hom ≫ n = v ≫ c.hom) : n ≫ c.inv = b.inv ≫ v := by
  have h2 : b.inv ≫ v = b.inv ≫ (v ≫ c.hom) ≫ c.inv := by simp
  rw [h2, ← h]
  simp

/-- **The second morphism of the dual triangle of the ideal sequence is multiplication by the
canonical section `1_D`**, read through `Stacks.Divisors.dualTriangleSecondVertexIso` and
`Stacks.Divisors.derivedDualIdealSheafIso`. -/
theorem dualTriangleSecondVertexIso_hom_comp_normalMor₁ :
    (dualTriangleSecondVertexIso D).hom ≫
        (normalShortComplex_shortExact D).singleTriangle.mor₁ =
      ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₁.op ≫
        (derivedDualIdealSheafIso D).hom := by
  have := isInvertible_unit_structureSheaf (X := X)
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (_root_.structureSheaf X.sheaf).property
      (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
    isInvertible_unit_structureSheaf
  have hnat := Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso_naturality X.sheaf
    (Stacks.IdealSheafSequence.divisorIdealMap D)
  have hb : (dualTriangleSecondVertexIso D).hom =
      (Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso X.sheaf
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0).map
          (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).hom :=
    rfl
  have hm : (normalShortComplex_shortExact D).singleTriangle.mor₁ =
      (DerivedCategory.singleFunctor X.Modules 0).map
        ((invertibleSheaf' D).unitHomEquiv.symm (canonicalSection' D)) := rfl
  rw [hb, hm]
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg
    ((Stacks.SheafOfModules.derivedSheafHomSingleStructureSheafIso X.sheaf
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).hom ≫ ·)
    ((((DerivedCategory.singleFunctor X.Modules 0).map_comp
        (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))).hom
        ((invertibleSheaf' D).unitHomEquiv.symm (canonicalSection' D))).symm).trans
      (congrArg (DerivedCategory.singleFunctor X.Modules 0).map
        (canonicalSectionHom_eq_internalHomPre D)))) ?_
  exact hnat.symm

/-- **The isomorphism assertion of [Stacks, Tag 0B4B], granted the first morphism of the dual
triangle.**

Suppose that, under the identification `Stacks.Divisors.dualTriangleSecondVertexIso` of the
second vertex `R ℰom(𝒪_X[0], 𝒪_X)` of the dual triangle of the ideal sequence with `𝒪_X[0]`, the
triangle's first morphism is the derived evaluation at one (`hmor₁`). Then
`Stacks.Divisors.normalShiftToDualTriangleVertex` is an isomorphism, which by
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_dualTriangleVertex` is
the isomorphism assertion of [Stacks, Tag 0B4B]. -/
theorem isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap
    (hmor₁ : ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
          (dualTriangleSecondVertexIso D).hom =
        (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
          derivedSheafHomEvaluationAtOne D) :
    IsIso (normalShiftToDualTriangleVertex D) := by
  set b := dualTriangleSecondVertexIso D
  obtain ⟨del, hdel⟩ := exists_distinguished_derivedDual_divisorIdeal D
  have hmor₂ : b.hom ≫ (normalShortComplex_shortExact D).singleTriangle.mor₁ =
      ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
        (divisorIdealShortComplex_shortExact D).singleTriangle.mor₁.op ≫
        (derivedDualIdealSheafIso D).hom :=
    dualTriangleSecondVertexIso_hom_comp_normalMor₁ D
  have hu : normalShiftToDualTriangleVertex D ≫
      ((derivedSheafHom X.sheaf).flip.obj
          (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
            (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫ b.hom =
      pushforwardNormalShift D := by
    refine (congrArg (fun t ↦ normalShiftToDualTriangleVertex D ≫ t) hmor₁).trans ?_
    change (pushforwardNormalShiftToDerivedSheafHom D ≫
        (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).hom) ≫
          ((derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
            derivedSheafHomEvaluationAtOne D) = _
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun t ↦ pushforwardNormalShiftToDerivedSheafHom D ≫ t)
      (Iso.hom_inv_id_assoc (derivedSheafHomPushforwardStructureSheafIsoDualVertex D)
        (derivedSheafHomEvaluationAtOne D))) ?_
    exact pushforwardNormalShiftToDerivedSheafHom_comp_derivedSheafHomEvaluationAtOne D
  have hmain : IsIso ((normalPushforwardShiftIso D).inv ≫
      normalShiftToDualTriangleVertex D) := by
    refine isIso_of_distTriang_of_forall_eq_zero_neg
      (inv_rot_of_distTriang _ (normalShortComplex_shortExact D).singleTriangle_distinguished)
      hdel _ b.symm (derivedDualIdealSheafIso D).symm
      (square_one (normalPushforwardShiftIso D) _ (pushforwardNormalShift D) _ _ b
        (normalPushforwardShiftIso_hom_comp_invRotate_mor₁ D) hu)
      (square_two _ _ b (derivedDualIdealSheafIso D) hmor₂) ?_
    intro w
    refine eq_zero_of_iso_comp_comp_eq_zero
      (((shiftFunctorCompIsoId (DerivedCategory X.Modules) (-1 : ℤ) 1 (by ring)).app
        (normalShortComplex_shortExact D).singleTriangle.obj₃).symm)
      (derivedDualIdealSheafIso D) ?_
    obtain ⟨w₀, hw₀⟩ := (DerivedCategory.singleFunctor X.Modules 0).map_surjective
      ((((shiftFunctorCompIsoId (DerivedCategory X.Modules) (-1 : ℤ) 1 (by ring)).app
          (normalShortComplex_shortExact D).singleTriangle.obj₃).symm).hom ≫ w ≫
        (derivedDualIdealSheafIso D).hom)
    refine hw₀.symm.trans ?_
    rw [hom_normalQuotient_divisorSheaf_eq_zero D w₀]
    exact (DerivedCategory.singleFunctor X.Modules 0).map_zero _ _
  exact IsIso.of_isIso_comp_left (normalPushforwardShiftIso D).inv _

/-- **The isomorphism assertion of [Stacks, Tag 0B4B]**, granted the first morphism of the dual
triangle of the ideal sequence: the canonical comparison morphism

`𝒩_{D/X}[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)`

of an effective Cartier divisor is an isomorphism. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap
    (hmor₁ : ((derivedSheafHom X.sheaf).flip.obj
            (DerivedCategory.Q.obj (RingedSite.structureSheafComplex (ringedSite X.sheaf)))).map
          (divisorIdealShortComplex_shortExact D).singleTriangle.mor₂.op ≫
          (dualTriangleSecondVertexIso D).hom =
        (derivedSheafHomPushforwardStructureSheafIsoDualVertex D).inv ≫
          derivedSheafHomEvaluationAtOne D) :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) :=
  (isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_dualTriangleVertex D).mpr
    (isIso_normalShiftToDualTriangleVertex_of_dualTriangleFirstMap D hmor₁)

end Stacks.Divisors

end
