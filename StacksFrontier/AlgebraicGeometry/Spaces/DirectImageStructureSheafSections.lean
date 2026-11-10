module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral

/-!
# Sections of the direct image of the structure sheaf over an étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `V` be an étale scheme chart of `Y`.
The sections of `f_*𝒪_X` over `V` are the regular functions on the algebraic space
`W = X ×_Y V`: a ring isomorphism identifies them with `AlgebraicGeometry.Space.globalFunctions`
of `W`, and under it the structure map `f♯ : 𝒪_Y(V) ⟶ (f_*𝒪_X)(V)` of Stacks 03G8 becomes
pullback of functions along the projection `W ⟶ V`.

## Main definitions

* `AlgebraicGeometry.Space.directImageGlobalFunctionsEquiv`: the ring isomorphism between the
  sections of `f_*𝒪_X` over `V` and the global functions of `X ×_Y V`.

## Main results

* `AlgebraicGeometry.Space.directImageGlobalFunctionsEquiv_structureSharp`: the structure map
  is pullback of functions along `X ×_Y V ⟶ V`.
* `AlgebraicGeometry.Space.bijective_structureSharp_app_iff`: the structure map is bijective
  on `V` exactly when pullback of functions along `X ×_Y V ⟶ V` is.
* `AlgebraicGeometry.Space.isIso_structureSharp_of_isAffine` and
  `AlgebraicGeometry.Space.isIso_structureSharp`: `f♯` is an isomorphism as soon as that
  pullback is bijective for every étale chart `V` of `Y` with affine source.

## Implementation notes

The sections of `f_*𝒪_X` over `V` are a limit over the étale scheme charts of `X` lying over
`W = X ×_Y V` (`AlgebraicGeometry.Space.chartIsLimit`), while the global functions of `W` are
a limit over the étale scheme charts of `W`. The two index categories have the same objects up
to the composition with the étale morphism `W ⟶ X`: a chart of `W` composed with `W ⟶ X` is a
chart of `X` over `W`, and conversely a morphism over `X` from a chart of `X` to `W` is a chart
of `W` by Stacks 03FV. The ring structure on the sections of the direct image is the
transported one of `Stacks.Sheaves.ToposPullback.ringObjRing`, so the comparison is read
through `AlgebraicGeometry.Space.chartProjection`, which is natural in the sheaf and therefore
commutes with the transported operations.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The étale scheme chart of `X` lying over `X ×_Y V` attached to an étale scheme chart of
`X ×_Y V`: the chart composed with the étale projection `X ×_Y V ⟶ X`. -/
noncomputable def chartOverBaseChange (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (φ : SmallEtale B S hS (chartBaseChange B S hS f V).1.left.1) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (Y := op (⟨CostructuredArrow.mk (φ.obj.hom ≫
      (chartBaseChange B S hS f V).1.hom.hom),
      (chartBaseChange B S hS f V).2 φ.obj.left φ.obj.hom φ.property⟩ : SmallEtale B S hS X.1))
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk φ.obj.hom)
      (ObjectProperty.hom_ext _ rfl))).op

/-- A morphism of étale scheme charts of `X ×_Y V` gives a morphism of the attached charts of
`X` lying over `X ×_Y V`. -/
noncomputable def chartOverBaseChangeMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {φ ψ : SmallEtale B S hS (chartBaseChange B S hS f V).1.left.1} (g : φ ⟶ ψ) :
    chartOverBaseChange B S hS f V ψ ⟶ chartOverBaseChange B S hS f V φ :=
  StructuredArrow.homMk (ObjectProperty.homMk (CostructuredArrow.homMk g.hom.left (by
    change yoneda.map g.hom.left ≫ ψ.obj.hom ≫ _ = φ.obj.hom ≫ _
    rw [← Category.assoc, CostructuredArrow.w g.hom])) :
      (chartOverBaseChange B S hS f V φ).right.unop ⟶
        (chartOverBaseChange B S hS f V ψ).right.unop).op (by
    apply Quiver.Hom.unop_inj
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
    exact CostructuredArrow.w g.hom)

/-- The étale scheme chart of `X ×_Y V` attached to an étale scheme chart of `X` lying over
`X ×_Y V`: a morphism over `X` between algebraic spaces étale over `X` is étale, by
Stacks 03FV. -/
noncomputable def baseChangeChartOfOver (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    SmallEtale B S hS (chartBaseChange B S hS f V).1.left.1 :=
  ⟨CostructuredArrow.mk j.hom.unop.hom.left.hom,
    (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS _)
        (chartBaseChange B S hS f V).1.left.2 X.2 j.hom.unop.hom.left.hom
        j.right.unop.obj.hom (chartBaseChange B S hS f V).1.hom.hom
        ((isEtale_iff_presheaf_of_yoneda B S hS _).2 j.right.unop.property)
        (chartBaseChange B S hS f V).2
        (congrArg (fun m => m.hom) (Over.w j.hom.unop.hom)))⟩

/-- A section of `f_*𝒪_X` over `V`, read on the étale scheme charts of `X ×_Y V`. -/
noncomputable def directImageToGlobalFunctions (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (a : (directImageSections B S hS f V).obj (structureSetSheaf B S hS X)) :
    globalFunctions B S hS (chartBaseChange B S hS f V).1.left.1 :=
  ⟨fun φ => (chartProjection B S hS f V (chartOverBaseChange B S hS f V φ.unop)).app
      (structureSetSheaf B S hS X) a, fun {φ ψ} g => by
    have e1 := chartProjection_app_apply B S hS f V (chartOverBaseChange B S hS f V φ.unop) a
    have e2 := chartProjection_app_apply B S hS f V (chartOverBaseChange B S hS f V ψ.unop) a
    have h := ((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X).op.ranCounit.app
        (structureSetSheaf B S hS X).obj)).coneAt
      (op (chartBaseChange B S hS f V))).π.naturality (chartOverBaseChangeMap B S hS f V g.unop)
    refine ((congrArg (fun x => (structurePresheaf B S hS _ ⋙ forget CommRingCat).map g x)
      e1).trans ?_).trans e2.symm
    exact (ConcreteCategory.congr_hom h a).symm⟩

/-- A morphism of étale scheme charts of `X` lying over `X ×_Y V` gives a morphism of the
attached charts of `X ×_Y V`. -/
noncomputable def baseChangeChartOfOverMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (m : j ⟶ j') :
    baseChangeChartOfOver B S hS f V j' ⟶ baseChangeChartOfOver B S hS f V j :=
  ObjectProperty.homMk (CostructuredArrow.homMk m.right.unop.hom.left (by
    have hw := congrArg (fun k => k.unop.hom.left.hom) (StructuredArrow.w m)
    exact hw))

/-- A global function of `X ×_Y V`, read as a section of `f_*𝒪_X` over `V`. -/
noncomputable def globalFunctionsToDirectImage (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (s : globalFunctions B S hS (chartBaseChange B S hS f V).1.left.1) :
    (directImageSections B S hS f V).obj (structureSetSheaf B S hS X) :=
  (Types.isLimitEquivSections (chartIsLimit B S hS f V)).symm
    ⟨fun j => s.val (op (baseChangeChartOfOver B S hS f V j)), fun {_ _} m =>
      s.property (baseChangeChartOfOverMap B S hS f V m).op⟩

/-- Reading a global function of `X ×_Y V` as a section of `f_*𝒪_X` and back gives it back. -/
theorem directImageToGlobalFunctions_globalFunctionsToDirectImage (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1) (s : globalFunctions B S hS (chartBaseChange B S hS f V).1.left.1) :
    directImageToGlobalFunctions B S hS f V (globalFunctionsToDirectImage B S hS f V s) = s := by
  refine Subtype.ext (funext fun φ => ?_)
  exact (chartProjection_app_apply B S hS f V (chartOverBaseChange B S hS f V φ.unop)
    (globalFunctionsToDirectImage B S hS f V s)).trans
    (Types.isLimitEquivSections_symm_apply _ _ _)

/-- The morphism comparing an étale scheme chart of `X` lying over `X ×_Y V` with the chart
rebuilt from the attached chart of `X ×_Y V`; its underlying morphism of schemes is the
identity. -/
noncomputable def toChartOverBaseChange (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    j ⟶ chartOverBaseChange B S hS f V (baseChangeChartOfOver B S hS f V j) :=
  StructuredArrow.homMk (ObjectProperty.homMk (CostructuredArrow.homMk
      (𝟙 j.right.unop.obj.left) (by
        have hw : j.hom.unop.hom.left.hom ≫ (chartBaseChange B S hS f V).1.hom.hom =
            j.right.unop.obj.hom := congrArg (fun m => m.hom) (Over.w j.hom.unop.hom)
        exact (Category.id_comp _).trans hw.symm)) :
      (chartOverBaseChange B S hS f V (baseChangeChartOfOver B S hS f V j)).right.unop ⟶
        j.right.unop).op (by
    apply Quiver.Hom.unop_inj
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
    exact Category.id_comp _)

/-- Projecting a section of `f_*𝒪_X` to the chart rebuilt from the attached chart of `X ×_Y V`
is projecting it to the original chart. -/
theorem chartProjection_chartOverBaseChange_baseChangeChartOfOver (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : (directImageSections B S hS f V).obj (structureSetSheaf B S hS X)) :
    (chartProjection B S hS f V
        (chartOverBaseChange B S hS f V (baseChangeChartOfOver B S hS f V j))).app
        (structureSetSheaf B S hS X) a =
      (chartProjection B S hS f V j).app (structureSetSheaf B S hS X) a := by
  have h := ((Functor.RightExtension.mk _
    ((comparisonFunctor B S hS X).op.ranCounit.app
      (structureSetSheaf B S hS X).obj)).coneAt
    (op (chartBaseChange B S hS f V))).π.naturality (toChartOverBaseChange B S hS f V j)
  have hid : ∀ x, ((StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙ (structureSetSheaf B S hS X).obj).map
        (toChartOverBaseChange B S hS f V j)) x = x := fun x => by
    change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 j.right.unop.obj.left)).op).hom x = x
    simp only [CategoryTheory.Functor.map_id, op_id]
    rfl
  refine (chartProjection_app_apply B S hS f V _ a).trans ?_
  refine ((ConcreteCategory.congr_hom h a).trans (hid _)).trans ?_
  exact (chartProjection_app_apply B S hS f V j a).symm

/-- Reading a section of `f_*𝒪_X` as a global function of `X ×_Y V` and back gives it back. -/
theorem globalFunctionsToDirectImage_directImageToGlobalFunctions (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (a : (directImageSections B S hS f V).obj (structureSetSheaf B S hS X)) :
    globalFunctionsToDirectImage B S hS f V (directImageToGlobalFunctions B S hS f V a) = a := by
  refine chartProjection_ext B S hS f V fun j => ?_
  refine (chartProjection_app_apply B S hS f V j _).trans ?_
  refine (Types.isLimitEquivSections_symm_apply _ _ _).trans ?_
  exact chartProjection_chartOverBaseChange_baseChangeChartOfOver B S hS f V j a

/-- **The sections of `f_*𝒪_X` over an étale chart `V` of `Y` are the global functions of
`X ×_Y V`**, as rings, the sections of the direct image carrying the ring structure transported
from the structure sheaf of `X`. -/
noncomputable def directImageGlobalFunctionsEquiv (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    letI := ringObjRing (structureRingSheaf B S hS X) (directImageSections B S hS f V)
    (directImageSections B S hS f V).obj (structureSetSheaf B S hS X) ≃+*
      globalFunctions B S hS (chartBaseChange B S hS f V).1.left.1 :=
  letI := ringObjRing (structureRingSheaf B S hS X) (directImageSections B S hS f V)
  { toFun := directImageToGlobalFunctions B S hS f V
    invFun := globalFunctionsToDirectImage B S hS f V
    left_inv := globalFunctionsToDirectImage_directImageToGlobalFunctions B S hS f V
    right_inv := directImageToGlobalFunctions_globalFunctionsToDirectImage B S hS f V
    map_mul' := fun a b => Subtype.ext (funext fun φ =>
      (ringMulObj_naturality (structureRingSheaf B S hS X)
        (chartProjection B S hS f V (chartOverBaseChange B S hS f V φ.unop)) a b).trans
        (sectionsFunctor_map_ringMulHom (structureRingSheaf B S hS X) _ _ _))
    map_add' := fun a b => Subtype.ext (funext fun φ =>
      (ringAddObj_naturality (structureRingSheaf B S hS X)
        (chartProjection B S hS f V (chartOverBaseChange B S hS f V φ.unop)) a b).trans
        (sectionsFunctor_map_ringAddHom (structureRingSheaf B S hS X) _ _ _)) }

/-- The isomorphism of `AlgebraicGeometry.Space.directImageGlobalFunctionsEquiv` reads a section
on an étale chart of `X ×_Y V` as its projection to the attached chart of `X`. -/
theorem directImageGlobalFunctionsEquiv_apply_val (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (a : (directImageSections B S hS f V).obj (structureSetSheaf B S hS X))
    (φ : (SmallEtale B S hS (chartBaseChange B S hS f V).1.left.1)ᵒᵖ) :
    (directImageGlobalFunctionsEquiv B S hS f V a).val φ =
      (chartProjection B S hS f V (chartOverBaseChange B S hS f V φ.unop)).app
        (structureSetSheaf B S hS X) a :=
  rfl

/-- **The structure map, read on global functions.** Under
`AlgebraicGeometry.Space.directImageGlobalFunctionsEquiv`, the chartwise structure map of
Stacks 03G8 on an étale chart `V` of `Y` is pullback of functions along the projection
`X ×_Y V ⟶ V`. -/
theorem directImageGlobalFunctionsEquiv_structureMapApp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (r : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)) :
    directImageGlobalFunctionsEquiv B S hS f V (structureMapApp B S hS f V r) =
      pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)) r :=
  Subtype.ext (funext fun φ =>
    chartProjection_structureMapApp B S hS f V (chartOverBaseChange B S hS f V φ.unop) r)

/-- **The structure map on an étale chart, through global functions.** The structure map
`f♯ : 𝒪_Y(V) ⟶ (f_*𝒪_X)(V)` of Stacks 03G8, followed by the identification of the sections of
the direct image with the global functions of `X ×_Y V`, is pullback of functions along the
projection `X ×_Y V ⟶ V`. -/
theorem directImageGlobalFunctionsEquiv_structureSharp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (r : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)) :
    directImageGlobalFunctionsEquiv B S hS f V
        ((directImageSectionsEquiv B S hS f V).symm
          (((structureSharp B S hS f).hom.app (op V)).hom r)) =
      pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)) r := by
  have h : (directImageSectionsEquiv B S hS f V).symm
      (((structureSharp B S hS f).hom.app (op V)).hom r) = structureMapApp B S hS f V r :=
    (directImageSectionsEquiv B S hS f V).symm_apply_apply _
  rw [h]
  exact directImageGlobalFunctionsEquiv_structureMapApp B S hS f V r

/-- **The structure map is bijective on an étale chart `V` of `Y` exactly when pullback of
functions along `X ×_Y V ⟶ V` is bijective**, that is, when the regular functions on `V` are
the global functions of `X ×_Y V`. -/
theorem bijective_structureSharp_app_iff (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Function.Bijective ((structureSharp B S hS f).hom.app (op V)).hom ↔
      Function.Bijective (pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V))) := by
  let := ringObjRing (structureRingSheaf B S hS X) (directImageSections B S hS f V)
  have hfun : ⇑(pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V))) =
      (directImageGlobalFunctionsEquiv B S hS f V ∘ (directImageSectionsEquiv B S hS f V).symm) ∘
        ((structureSharp B S hS f).hom.app (op V)).hom :=
    funext fun r => (directImageGlobalFunctionsEquiv_structureSharp B S hS f V r).symm
  rw [hfun]
  exact (Function.Bijective.of_comp_iff'
    ((directImageGlobalFunctionsEquiv B S hS f V).bijective.comp
      (directImageSectionsEquiv B S hS f V).symm.bijective) _).symm

/-- **`f♯ : 𝒪_Y ⟶ f_*𝒪_X` is an isomorphism as soon as, for every étale chart `V` of `Y` with
affine source, the regular functions on `V` are the global functions of `X ×_Y V`.** The affine
étale charts are a dense subsite of the small étale site (Stacks 04JS), so a morphism of
sheaves is an isomorphism once it is bijective on affine charts. -/
theorem isIso_structureSharp_of_isAffine (f : X ⟶ Y)
    (h : ∀ V : SmallEtale B S hS Y.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
      Function.Bijective (pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)))) :
    IsIso (structureSharp B S hS f) := by
  have hsub : (AffineEtale.inclusion B S hS Y.1).IsDenseSubsite
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  refine Functor.IsCoverDense.iso_of_restrict_iso (G := AffineEtale.inclusion B S hS Y.1)
    (structureSharp B S hS f) ?_
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj U.unop.obj)) := U.unop.property
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ((bijective_structureSharp_app_iff B S hS f U.unop.obj).2 (h U.unop.obj this))

/-- **`f♯ : 𝒪_Y ⟶ f_*𝒪_X` is an isomorphism as soon as, for every étale chart `V` of `Y`, the
regular functions on `V` are the global functions of `X ×_Y V`.** -/
theorem isIso_structureSharp (f : X ⟶ Y)
    (h : ∀ V : SmallEtale B S hS Y.1,
      Function.Bijective (pullbackToGlobalFunctions B S hS (chartBaseChange B S hS f V).1.left
        ((SmallEtale.toOver B S hS Y.1).obj V)
        ((spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj V)))) :
    IsIso (structureSharp B S hS f) :=
  isIso_structureSharp_of_isAffine B S hS f fun V _ => h V

end AlgebraicGeometry.Space

end
