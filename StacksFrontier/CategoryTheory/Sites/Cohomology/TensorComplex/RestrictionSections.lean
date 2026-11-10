module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexRestriction

/-!
# The restriction comparison of the total tensor complex on local pure tensors

Let `X` be a ringed site, `U` an object of its underlying category and `A`, `B` complexes of
`O`-modules. The comparison

`(Tot(A ⊗_O B))|_U ≅ Tot(A|_U ⊗_{O|_U} B|_U)`

is `AlgebraicGeometry.RingedSite.tensorComplexOverIso` for the `tensorComplex` construction of
the total tensor complex. It is assembled out of the comparison of a functor with a total
complex and an identification of two bicomplexes, so it is pinned on the *summands* of the
bicomplex and not on the local pure tensors, and no consumer of the total tensor complex in this
development is phrased in terms of summands.

This file computes it on the pure tensors: it carries the pure tensor of two local sections,
formed on the site over `U`, to the pure tensor of the same two sections formed on `X`. The
restriction to a slice only reindexes the sections, so there is nothing else for it to do, and
in particular no sign.

## Main results

* `AlgebraicGeometry.RingedSite.ι_tensorComplexOverIso_inv`: the comparison on a summand of the
  bicomplex.
* `AlgebraicGeometry.RingedSite.tensorComplexOverIso_inv_tensorComplexSection`: the comparison
  on a local pure tensor.
* `AlgebraicGeometry.RingedSite.tensorTotalOverIso_hom_tensorTotalSectionAt`: the same in the
  direct direction, which is the one a consumer pushing a section from `X` to the slice wants.
* `AlgebraicGeometry.RingedSite.tensorTotalOverIso_inv_tensorTotalSectionAt`: **the same for
  `AlgebraicGeometry.RingedSite.tensorTotalOverIso`**, the comparison in the spelling of the
  total tensor complex that this development's consumers use. It carries the pure tensor formed
  on the site over `U` to the pure tensor formed on `X`, in the same total degree and with no
  sign. This is the statement the restriction compatibility of the interchange morphism of
  Stacks 0BYR will be checked against.

## Implementation notes

Both statements are about the **inverse** of the comparison. That is the direction in which
everything in sight is characterised: the comparison of a functor with a total complex is
defined out of the coproduct, so `HomologicalComplex₂.TotalMap.ι_totalMapf` describes it on a
summand, and `AlgebraicGeometry.RingedSite.sheafTensorOverIso` is built by
`AlgebraicGeometry.RingedSite.isoOfUnits`, whose *inverse* is the one of its two legs that
`AlgebraicGeometry.RingedSite.comp_liftOfUnit` describes on the sheafification unit. A consumer
wanting the other direction applies the isomorphism to both sides.

Neither proof uses `rw`, and not by preference. Once
`AlgebraicGeometry.RingedSite.tensorComplexOverIso` is unfolded, the goal mentions
`restrictComplex X (Tot(A ⊗_O B)) U` on one side and the total complex of the restricted
bicomplex on the other; these are the same complex, but only at default transparency, so the
goal is not type-correct at the transparency a rewrite works at and even `Category.assoc` fails
to apply. The proofs are therefore built as terms, with the unfolding pinned once by the
definitional equation `tensorComplexOverIso_inv_f`. The instances that
`tensorComplexOverIso` introduces by `have` inside its own proof have to be reproduced, for the
same reason: they are part of the term and not available to synthesis from outside.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor Stacks.SheafOfModules.UliftTensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.tensorComplex
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [sliceSheafify : HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [sliceLocallyBijective : (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [sliceTensorAdditive : (sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [sliceTensorObjAdditive :
    ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U)),
      ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [sliceTensorHasMap : ∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.O.over U))) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} (X.O.over U))
      (ComplexShape.up ℤ)]
  (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The restriction comparison, unfolded.** Its inverse is the map of total complexes induced
by the identification of the two bicomplexes, followed by the comparison of the restriction
functor with the total complex. This holds by definition, and is stated because the unfolded
goal is not type-correct at the transparency a rewrite works at; pinning the unfolding as an
equation is what lets the computation proceed. -/
lemma tensorComplexOverIso_inv_f (c : ℤ) :
    (tensorComplexOverIso X U A B).inv.f c =
      (HomologicalComplex₂.total.map (overSheafTensorBicomplexIso X U A B).inv
          (ComplexShape.up ℤ)).f c ≫
        HomologicalComplex₂.TotalMap.totalMapf
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
          (sheafTensorBicomplex X A B) c :=
  rfl

/-- **The restriction comparison on a summand of the bicomplex.** On the summand of index
`(t, r)` the inverse of the comparison is the objectwise comparison
`AlgebraicGeometry.RingedSite.sheafTensorOverIso` of that term, followed by the restriction of
the inclusion of the corresponding summand on `X`. -/
lemma ι_tensorComplexOverIso_inv (t r c : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (t, r) = c) :
    (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫
        (tensorComplexOverIso X U A B).inv.f c =
      (sheafTensorOverIso X U (A.X t) (B.X r)).inv ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          ((sheafTensorBicomplex X A B).ιTotal (ComplexShape.up ℤ) t r c h) := by
  have hpc : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  have hpc0 : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    preservesColimitsOfSize_shrink _
  have hht : HomologicalComplex₂.HasTotal
      (HomologicalComplex₂.TotalMap.mapBicomplex
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
        (sheafTensorBicomplex X A B))
      (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso (overSheafTensorBicomplexIso X U A B).symm _
  have e1 := HomologicalComplex₂.ιTotal_map _ _
    (overSheafTensorBicomplexIso X U A B).inv (ComplexShape.up ℤ) t r c h
  have e2 := HomologicalComplex₂.TotalMap.ι_totalMapf
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (sheafTensorBicomplex X A B) c t r h
  refine Eq.trans (congrArg
    (fun z => (overSheafTensorBicomplex X U A B).ιTotal (ComplexShape.up ℤ) t r c h ≫ z)
    (tensorComplexOverIso_inv_f X U A B c)) ?_
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ HomologicalComplex₂.TotalMap.totalMapf
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
      (sheafTensorBicomplex X A B) c) e1)).trans
    ((Category.assoc _ _ _).trans (congrArg
      (fun z => (((overSheafTensorBicomplexIso X U A B).inv.f t).f r) ≫ z) e2))

/-- **The restriction comparison on a local pure tensor.** The inverse of the comparison carries
the homogeneous local pure tensor of two sections, formed on the site over `U`, to the pure
tensor of the same two sections formed on `X`. There is no sign and no transport: restriction to
a slice reindexes the sections and does nothing else. -/
lemma tensorComplexOverIso_inv_tensorComplexSection
    (W : (X.over U).C) (t r c : ℤ) (h : t + r = c)
    (a : ((restrictComplex X A U).X t).val.obj (op W))
    (b : ((restrictComplex X B U).X r).val.obj (op W)) :
    ((tensorComplexOverIso X U A B).inv.f c).val.app (op W)
        (@tensorComplexSection.{u} (X.over U) sliceSheafify sliceLocallyBijective
          sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap
          (restrictComplex X A U) (restrictComplex X B U) t r c h W a b) =
      tensorComplexSection X t r c h a b := by
  have := isLocallyInjective_sheafifyUnit (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    (overTensorPresheaf X U (A.X t) (B.X r))
  have := isLocallySurjective_sheafifyUnit
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    (overTensorPresheaf X U (A.X t) (B.X r))
  refine Eq.trans (congrArg (fun z => z.val.app (op W)
    ((sheafifyUnit (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (overTensorPresheaf X U (A.X t) (B.X r))).app (op W)
        (a ⊗ₜ[((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op W)] b)))
    (ι_tensorComplexOverIso_inv X U A B t r c (by simpa using h))) ?_
  exact congrArg (fun z => ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((sheafTensorBicomplex X A B).ιTotal (ComplexShape.up ℤ) t r c
        (by simpa using h))).val.app (op W) z)
    (congrArg (fun z => z.app (op W)
        (a ⊗ₜ[((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj (op W)] b))
      (comp_liftOfUnit (sheafifyUnit (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
          (overTensorPresheaf X U (A.X t) (B.X r)))
        ((overPresheafTensorIso X U (A.X t) (B.X r)).inv ≫
          overSheafifyUnit X U (PresheafOfModules.tensorObj (A.X t).val (B.X r).val))))

/-! ### The comparison in the `tensorTotal` spelling -/

/-- Transposing an identity about the inverse of an isomorphism of complexes into one about its
direct part, on a local section in a fixed degree. -/
private lemma iso_hom_val_app_of_inv {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}}
    {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (e : K ≅ L) (c : ℤ) (V : Dᵒᵖ)
    (x : (K.X c).val.obj V) (y : (L.X c).val.obj V)
    (hy : (e.inv.f c).val.app V y = x) :
    (e.hom.f c).val.app V x = y := by
  subst hy
  exact congrArg
    (fun z => (SheafOfModules.Hom.val (HomologicalComplex.Hom.f z c)).app V y) e.inv_hom_id

/-- The sheaf tensor product of the localized site is additive, at the spelling `(X.over U).O`
of its structure sheaf, using the dictionary for `X.O.over U`. -/
local instance sliceSheafTensorAdditive : (sheafTensor.{u, u, u, u, u} (X.over U).O).Additive :=
  sliceTensorAdditive

/-- Tensoring with a fixed sheaf of modules on the localized site is additive, at the spelling
`(X.over U).O` of its structure sheaf. -/
local instance sliceSheafTensorObjAdditive
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :
    ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive :=
  sliceTensorObjAdditive M

/-- **The comparison of `AlgebraicGeometry.RingedSite.tensorTotalOverIso`, unfolded.** Its
inverse is the identification of the two total tensor complexes on the localized site, the
inverse of the comparison for `tensorComplex`, and the restriction of the identification of the
two total tensor complexes on `X`. This holds by definition. -/
lemma tensorTotalOverIso_inv_f (c : ℤ) :
    (tensorTotalOverIso X U A B).inv.f c =
      (((@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
            sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
            (restrictComplex X B U)).hom.f c) ≫
          ((tensorComplexOverIso X U A B).inv.f c)) ≫
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          ((tensorTotalIsoTensorComplex X A B).inv.f c)) :=
  rfl

/-- **The restriction comparison of the total tensor complex on a local pure tensor.** The
inverse of

`(Tot(A ⊗_O B))|_U ≅ Tot(A|_U ⊗_{O|_U} B|_U)`

carries the homogeneous local pure tensor of a degree-`t` section of `A|_U` and a degree-`r`
section of `B|_U` over an object `W` of the site over `U`, read in the degree `c`, to the pure
tensor of the same two sections over the underlying object of `X`, read in the same degree `c`.

There is no sign and no change of degree: restricting to a slice reindexes the sections and does
nothing else. The three legs of the comparison contribute, in order, the identification of the
two constructions of the total tensor complex on the slice, the comparison for `tensorComplex`,
and the restriction of that identification on `X`; each is already known on the pure
tensors. -/
lemma tensorTotalOverIso_inv_tensorTotalSectionAt
    (W : (X.over U).C) (t r c : ℤ) (h : t + r = c)
    (a : ((restrictComplex X A U).X t).val.obj (op W))
    (b : ((restrictComplex X B U).X r).val.obj (op W)) :
    ((tensorTotalOverIso X U A B).inv.f c).val.app (op W)
        (tensorTotalSectionAt (X.over U) (restrictComplex X A U) (restrictComplex X B U)
          W t r c h a b) =
      tensorTotalSectionAt X A B W.left t r c h a b := by
  have hA : ((@tensorTotalIsoTensorComplex.{u} (X.over U) sliceSheafify sliceLocallyBijective
        sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap (restrictComplex X A U)
        (restrictComplex X B U)).hom.f c).val.app (op W)
      (tensorTotalSectionAt (X.over U) (restrictComplex X A U) (restrictComplex X B U)
        W t r c h a b) =
      @tensorComplexSection.{u} (X.over U) sliceSheafify sliceLocallyBijective
        sliceTensorAdditive sliceTensorObjAdditive sliceTensorHasMap
        (restrictComplex X A U) (restrictComplex X B U) t r c h W a b :=
    iso_hom_val_app_of_inv _ c (op W) _ _
      (@tensorTotalIsoTensorComplex_inv_tensorComplexSection.{u} (X.over U)
        sliceSheafify sliceLocallyBijective sliceTensorAdditive sliceTensorObjAdditive
        sliceTensorHasMap
        (restrictComplex X A U) (restrictComplex X B U) W t r c h a b)
  have hB := tensorComplexOverIso_inv_tensorComplexSection X U A B W t r c h a b
  have hC := tensorTotalIsoTensorComplex_inv_tensorComplexSection X A B W.left t r c h a b
  refine Eq.trans (congrArg (fun z => (SheafOfModules.Hom.val z).app (op W)
    (tensorTotalSectionAt (X.over U) (restrictComplex X A U) (restrictComplex X B U)
      W t r c h a b)) (tensorTotalOverIso_inv_f X U A B c)) ?_
  refine Eq.trans (congrArg (fun y =>
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
        ((tensorTotalIsoTensorComplex X A B).inv.f c)).val.app (op W)
      (((tensorComplexOverIso X U A B).inv.f c).val.app (op W) y)) hA) ?_
  exact Eq.trans (congrArg (fun y =>
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((tensorTotalIsoTensorComplex X A B).inv.f c)).val.app (op W) y) hB) hC

/-- **The restriction comparison of the total tensor complex on a local pure tensor, in the
direct direction.** The comparison carries the pure tensor of two sections formed on `X`, read
over an object `W` of the site over `U`, to the pure tensor of the same two sections formed on
the site over `U`, in the same total degree and with no sign.

This is `AlgebraicGeometry.RingedSite.tensorTotalOverIso_inv_tensorTotalSectionAt` transposed.
It is the direction a consumer wants when it has a section on `X` in hand and is pushing it to
the slice, which is what comparing a morphism with its restriction amounts to. -/
lemma tensorTotalOverIso_hom_tensorTotalSectionAt
    (W : (X.over U).C) (t r c : ℤ) (h : t + r = c)
    (a : ((restrictComplex X A U).X t).val.obj (op W))
    (b : ((restrictComplex X B U).X r).val.obj (op W)) :
    ((tensorTotalOverIso X U A B).hom.f c).val.app (op W)
        (tensorTotalSectionAt X A B W.left t r c h a b) =
      tensorTotalSectionAt (X.over U) (restrictComplex X A U) (restrictComplex X B U)
        W t r c h a b :=
  iso_hom_val_app_of_inv _ c (op W) _ _
    (tensorTotalOverIso_inv_tensorTotalSectionAt X U A B W t r c h a b)

end AlgebraicGeometry.RingedSite

end
