module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctions

/-!
# The sections of a direct image over an étale chart are the global functions of the fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and `V` an étale scheme chart of `Y`.
`AlgebraicGeometry.Space.directImageSectionsToGlobalFunctions` reads a section of `f_* 𝒪_X` over
`V` as a global regular function on the algebraic space `X ×_Y V`, and is injective. This file
shows that it is **bijective**: the étale scheme charts of `X` above `X ×_Y V`, which index the
limit computing the sections of the direct image, are the étale scheme charts of `X ×_Y V`, so a
compatible family of regular functions on the latter is a compatible family on the former.

## Main definitions

* `AlgebraicGeometry.Space.indexChart`: the étale scheme chart of `X ×_Y V` attached to an index
  of the limit of chart sections.
* `AlgebraicGeometry.Space.directImageSectionsGlobalFunctionsEquiv`: the ring isomorphism
  `(f_* 𝒪_X)(V) ≃+* Γ(X ×_Y V, 𝒪)`.

## Main results

* `AlgebraicGeometry.Space.surjective_directImageSectionsToGlobalFunctions` and
  `AlgebraicGeometry.Space.bijective_directImageSectionsToGlobalFunctions`.

## References

* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The étale scheme chart of `X ×_Y V` attached to an index of the limit of chart sections: an
étale scheme chart of `X` with a morphism over `X` to `X ×_Y V`, which is étale since both are
étale over `X`. -/
def indexChart (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj :=
  ⟨CostructuredArrow.mk j.hom.unop.hom.left.hom,
    presheaf_etale_of_isEtale B S hS (isEtale_of_isEtale_over B S hS
      (isAlgebraicSpace_yoneda B S hS _) (chartBaseChangeSpace B S hS f V).property X.property
      j.hom.unop.hom.left.hom _ (chartBaseChange B S hS f V).obj.hom.hom
      (isEtale_of_presheaf_etale B S hS j.right.unop.2) (chartBaseChange B S hS f V).property
      (congrArg (fun k => k.hom) (Over.w j.hom.unop.hom)))⟩

/-- A morphism of indices, read as a morphism of the attached charts of `X ×_Y V`. -/
def indexChartMap (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂) : indexChart B S hS f V j₂ ⟶ indexChart B S hS f V j₁ :=
  ObjectProperty.homMk (CostructuredArrow.homMk ((SmallEtale.toOver B S hS X.1).map φ.right.unop)
    (congrArg (fun k => k.unop.hom.left.hom) (StructuredArrow.w φ)))

/-- The cone of the values of a global function on `X ×_Y V` at the charts attached to the
indices of the limit of chart sections. -/
def globalFunctionsCone (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (s : globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj) :
    Cone (StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙ (structureSetSheaf B S hS X).obj) where
  pt := PUnit
  π :=
    { app := fun j => TypeCat.ofHom fun _ => s.val (op (indexChart B S hS f V j))
      naturality := fun j₁ j₂ φ => by
        ext
        exact (s.property (indexChartMap B S hS f V φ).op).symm }

/-- **The map from the sections of `f_* 𝒪_X` over `V` to the global functions on `X ×_Y V` is
surjective**: a global function is the limit of its values on the charts of `X` above
`X ×_Y V`, which are charts of `X ×_Y V`. -/
theorem surjective_directImageSectionsToGlobalFunctions (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Function.Surjective (directImageSectionsToGlobalFunctions B S hS f V) := by
  intro s
  let x := (chartIsLimit B S hS f V).lift (globalFunctionsCone B S hS f V s) PUnit.unit
  refine ⟨(directImageRanComparison B S hS f V).hom x, Subtype.ext (funext fun c => ?_)⟩
  have hcancel : ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureSetSheaf B S hS X)).hom.app (op V)
      (((smallEtaleDirectImageRanIso B S hS f).inv.app (structureSetSheaf B S hS X)).hom.app
        (op V) x) = x :=
    Sheaf.hom_congr_app_apply
      (((smallEtaleDirectImageRanIso B S hS f).app (structureSetSheaf B S hS X)).inv_hom_id)
      (op V) x
  have hfac := congrArg (fun k => k PUnit.unit)
    ((chartIsLimit B S hS f V).fac (globalFunctionsCone B S hS f V s)
      (baseChangeSpaceChartIndex B S hS f V c.unop))
  refine (congrArg ((chartProjection B S hS f V (baseChangeSpaceChartIndex B S hS f V
    c.unop)).app (structureSetSheaf B S hS X)) hcancel).trans ?_
  exact (chartProjection_app_apply B S hS f V _ x).trans hfac

/-- **The map from the sections of `f_* 𝒪_X` over `V` to the global functions on `X ×_Y V` is
bijective.** -/
theorem bijective_directImageSectionsToGlobalFunctions (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Function.Bijective (directImageSectionsToGlobalFunctions B S hS f V) :=
  ⟨injective_directImageSectionsToGlobalFunctions B S hS f V,
    surjective_directImageSectionsToGlobalFunctions B S hS f V⟩

/-- **The sections of `f_* 𝒪_X` over an étale chart `V` of `Y` are the global regular functions
on `X ×_Y V`**, as rings. -/
def directImageSectionsGlobalFunctionsEquiv (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    (pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op V) ≃+*
      globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj :=
  RingEquiv.ofBijective _ (bijective_directImageSectionsToGlobalFunctions B S hS f V)

end AlgebraicGeometry.Space

end
