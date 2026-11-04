module

public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic

/-!
# The projection formula for a closed immersion

For a morphism of ringed spaces `f : Z ⟶ X` there is a canonical morphism

`f_* 𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^* ℋ)`,

the adjoint transpose of the pullback tensor comparison of [Stacks, Tag 01CD] followed by the
counit of `f^* ⊣ f_*` in the first factor.  This file constructs that morphism for an arbitrary
morphism of ringed spaces, records its naturality in both arguments and its compatibility with
the tensorized unit, and proves that it is an isomorphism when `f` is a closed quotient morphism
— a homeomorphism onto a closed subset whose comorphism of structure sheaves is surjective, in
particular a closed immersion of schemes.

## Main definitions

* `CategoryTheory.adjunctionTensorMap`: the canonical map in the abstract setting
  of an adjunction together with a tensor bifunctor upstairs and downstairs and a comparison
  between them.  Its two naturality statements are proved here once and for all.
* `Stacks.AffineProjectionFormula.projectionFormulaMap`: the canonical map above, for an
  arbitrary morphism of ringed spaces.
* `Stacks.AffineProjectionFormula.projectionFormulaIso`: that map as an isomorphism for a closed
  quotient morphism of ringed spaces.
* `Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso`: the same for a closed
  immersion of schemes.

## Main results

* `Stacks.AffineProjectionFormula.projectionFormulaMap_natural` and
  `projectionFormulaMap_natural_unit`: naturality in both module arguments, and the
  identification of the tensorized unit followed by the projection-formula map with the adjoint
  transpose of the pullback tensor comparison.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap`: **the projection formula for a
  closed quotient morphism.**
* `Stacks.AffineProjectionFormula.smul_tensorSheaf_eq_zero`: a section of the structure sheaf
  which annihilates a module annihilates every tensor product with it on the left.

## The argument

Writing the canonical map through the unit, `adj.homEquiv φ = η ≫ f_*φ`, it becomes the composite

`f_*𝒢 ⊗ ℋ --η--> f_* f^*(f_*𝒢 ⊗ ℋ) --f_*(comparison)--> f_*(f^*f_*𝒢 ⊗ f^*ℋ)
   --f_*(ε ⊗ 1)--> f_*(𝒢 ⊗ f^*ℋ)`

and each of the three factors is invertible for a closed quotient morphism:

* the comparison is [Stacks, Tag 01CD], unconditionally
  (`Stacks.RingedSpace.comparisonNatTrans_app_isIso`);
* the counit `ε : f^*f_*𝒢 ⟶ 𝒢` is invertible because `f_*` is fully faithful, which is the
  full-faithfulness half of [Stacks, Tag 08KS], proved for a closed quotient morphism as
  `ClosedQuotientMorphismOfRingedSpaces.fullyFaithfulModulePushforward`;
* the unit at `f_*𝒢 ⊗ ℋ` is invertible because that module lies in the essential image of `f_*`,
  which by the essential-image half of [Stacks, Tag 08KS] is the condition that the kernel ideal
  `ℐ = ker f^♯` annihilate it.  It does: `ℐ` annihilates `f_*𝒢`, whose scalars act through
  `f^♯`, and a scalar annihilating one factor of a tensor product annihilates the product.

So **no affine-local computation and no stalkwise argument is needed** for a closed immersion.
The last point is the only new mathematics, and it is proved stalkwise: a section is determined
by its germs (`Stacks.RingedSpace.section_ext_grpGerm`), the germ of a scalar multiple is the
multiple of the germs (`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul`), and
  the stalk of a tensor product
is the tensor product of the stalks (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`,
  [Stacks, Tag 01CB]), where a
scalar killing the left factor kills every pure tensor.

## Implementation notes

The generality here is a *closed* quotient morphism, not an affine morphism.  [Stacks, Tag 0FZE]
states the formula for an affine morphism `h : T ⟶ S` and quasi-coherent modules,
`h_*𝒢 ⊗_{𝒪_S} ℋ = h_*(𝒢 ⊗_{𝒪_T} h^*ℋ)`, and its proof is the translation into algebra over an
affine open of the target.  No declaration here is tagged `0FZE`: what is proved is a special
case of it, and the hypothesis `IsClosedImmersion` is not a hypothesis of the source statement.

That route needs the identification of the tensor product of two quasi-coherent modules on an
affine scheme with the tilde of the tensor product of their global sections ([Stacks, Tag 01I8]),
and it is available: Tag 01I8 is `AlgebraicGeometry.tildeTensorIso`, together with
`AlgebraicGeometry.tildeTensorIso_hom_tmul` and `AlgebraicGeometry.tildeTensorIso_natural`;
`AlgebraicGeometry.isQuasicoherentTensorSectionsIso` packages it as
`Γ(Spec R, F ⊗ G) ≅ Γ(Spec R, F) ⊗_R Γ(Spec R, G)` for quasi-coherent `F` and `G`, which is the
form an affine-local argument consumes.  The locality steps exist as well:
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` reduces invertibility of a
morphism of `Scheme.Modules` to an open covering, and
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` reduces it,
on an affine scheme and for quasi-coherent modules, to global sections.  The algebra identity
the source means by "translating into algebra" is Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, already wrapped as an isomorphism of
`ModuleCat` by `CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso`.

What `0FZE` still needs is therefore neither of those, and it is *not* a strengthening of the
argument above.  For a general affine morphism the counit `ε : f^*f_*𝒢 ⟶ 𝒢` is **not**
invertible: `isIso_counit_app` asks for `f_*` to be full and faithful, and that is exactly what
[Stacks, Tag 08KS] characterises for the closed case, while a finite morphism is affine and is
not a closed immersion.  So the three-factor argument does not generalise.

The ingredients of an affine-local proof are all present.  Besides the two reductions above,
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` restricts a direct image to
an open of the target, `Stacks.SheafOfModules.TensorOver.tensorOverIso` restricts a tensor
product, and `pushforward_isQuasicoherent_of_isAffineHom` in the same file as the first keeps
quasi-coherence along an affine morphism.  What no declaration in this repository supplies is
the compatibility of `projectionFormulaMap` *itself* with those restrictions, and the
identification, over an affine open of the target, of its effect on global sections with the
algebra isomorphism above — "the canonical map restricts to the canonical map" lemmas, of which
this map has none.  That, and not Tag 01I8, is the residue of `0FZE`.

The statements below use the canonical tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor`, uncurried when a morphism of the product category
is required. Its objectwise and bifunctor applications need no intervening comparison.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

universe u

/-! ### The counit of a fully faithful right adjoint -/

section Counit

variable {C : Type*} {D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- For an adjunction `L ⊣ R` with `R` fully faithful, every component of the counit is an
isomorphism.  The unit at `R.obj Y` is invertible, the right triangle exhibits `R.map (ε.app Y)`
as its inverse, and a fully faithful functor reflects isomorphisms. -/
lemma isIso_counit_app (adj : L ⊣ R) [R.Full] [R.Faithful] (Y : D) :
    IsIso (adj.counit.app Y) :=
  have : IsIso (R.map (adj.counit.app Y)) :=
    isIso_of_hom_comp_eq_id _ (adj.right_triangle_components Y)
  isIso_of_reflects_iso _ R

end Counit

/-! ### The canonical map, abstractly

An adjunction `L ⊣ R`, a bifunctor `A` on the base of `R`, a bifunctor `B` on its target and a
comparison `α : A ⋙ L ⟶ L × L ⋙ B` determine a map `A(R G, H) ⟶ R (B(G, L H))`.  Both naturality
statements of the projection formula are instances of the two lemmas proved here. -/

section Abstract

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

end Abstract

/-! ### Annihilation of a tensor product -/

section Annihilator

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- If a section `a` of the structure sheaf over `U` annihilates every section of `M` over every
open contained in `U`, then its germ at a point of `U` annihilates the whole stalk of `M`.  Every
stalk element is a germ, and after restricting both representatives to a common open the claim is
the characterisation `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul` of the
  stalk module structure. -/
lemma ringGerm_smul_eq_zero (M : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) (a : X.presheaf.obj (op U)) (p : X.carrier) (hp : p ∈ U)
    (hM : ∀ (V : Opens X.carrier) (hVU : V ≤ U) (m : M.val.obj (op V)),
      (X.presheaf.map (homOfLE hVU).op a) • m = 0)
    (m : grpStalk X M.val p) :
    ringGerm X p U hp a • m = 0 := by
  have key : ∀ (V : Opens X.carrier) (hpV : p ∈ V) (hVU : V ≤ U) (tV : M.val.obj (op V)),
      ringGerm X p V hpV ((X.presheaf.map (homOfLE hVU).op) a) •
        grpGerm X M.val p V hpV tV = 0 := by
    intro V hpV hVU tV
    rw [← stalkModule_germ_smul, hM V hVU, map_zero]
  obtain ⟨W, hpW, t, ht⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) (X := X.carrier) M.val.presheaf m
  have ht' : grpGerm X M.val p W hpW t = m := ht
  subst ht'
  have hpV : p ∈ W ⊓ U := ⟨hpW, hp⟩
  have hVW : W ⊓ U ≤ W := inf_le_left
  have hVU : W ⊓ U ≤ U := inf_le_right
  have e1 : grpGerm X M.val p (W ⊓ U) hpV ((M.val.map (homOfLE hVW).op) t)
      = grpGerm X M.val p W hpW t :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf
      (homOfLE hVW) p hpV t
  have e2 : ringGerm X p (W ⊓ U) hpV ((X.presheaf.map (homOfLE hVU).op) a)
      = ringGerm X p U hp a :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) p hpV a
  have h3 := key (W ⊓ U) hpV hVU ((M.val.map (homOfLE hVW).op) t)
  rw [e1, e2] at h3
  exact h3

/-- A section of the structure sheaf annihilating the left factor annihilates the tensor product.
A section is determined by its germs, the germ of a scalar multiple is the multiple of the germs,
and on the stalk the tensor product of the stalks is killed because its left factor is. -/
lemma smul_tensorSheaf_eq_zero (M N : SheafOfModules.{u} (structureSheafRing X))
    (U : Opens X.carrier) (a : X.presheaf.obj (op U))
    (hM : ∀ (V : Opens X.carrier) (hVU : V ≤ U) (m : M.val.obj (op V)),
      (X.presheaf.map (homOfLE hVU).op a) • m = 0)
    (s : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (M)).obj (N))).val.obj (op U)) :
    a • s = 0 := by
  refine Stacks.RingedSpace.section_ext_grpGerm
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (M)).obj (N))) U _ 0 ?_
  intro p hp
  have hten : ∀ y : (grpStalk X M.val p) ⊗[ringStalk X p] (grpStalk X N.val p),
      ringGerm X p U hp a • y = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
        rw [TensorProduct.smul_tmul', ringGerm_smul_eq_zero M U a p hp hM m,
          TensorProduct.zero_tmul]
    | add y₁ y₂ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]
  rw [map_zero, stalkModule_germ_smul]
  refine (tensorStalkIso X p M N).injective ?_
  rw [map_smul, map_zero]
  exact hten _

end Annihilator

/-! ### The projection-formula map for a morphism of ringed spaces -/

section Map

variable {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)

/-- **The canonical projection-formula map** `f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` for an
arbitrary morphism of ringed spaces: the adjoint transpose of the pullback tensor comparison of
[Stacks, Tag 01CD] followed by the counit of `f^* ⊣ f_*` in the first factor. -/
def projectionFormulaMap (G : SheafOfModules.{u} (structureRingSheaf Z))
    (H : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).obj ((pushforwardFunctor f).obj G, H) ⟶
      (pushforwardFunctor f).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj (G, (pullbackFunctor f).obj H)) :=
  adjunctionTensorMap (pullbackAdjunction f) ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)))
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))) (comparisonNatTrans f) G H

/-- The projection-formula map, written through the unit of `f^* ⊣ f_*`. -/
lemma projectionFormulaMap_eq_unit_comp (G : SheafOfModules.{u} (structureRingSheaf Z))
    (H : SheafOfModules.{u} (structureRingSheaf X)) :
    projectionFormulaMap f G H =
      (pullbackAdjunction f).unit.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).obj ((pushforwardFunctor f).obj G, H)) ≫
        (pushforwardFunctor f).map
          ((comparisonNatTrans f).app ((pushforwardFunctor f).obj G, H) ≫
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map
              ((pullbackAdjunction f).counit.app G ×ₘ 𝟙 ((pullbackFunctor f).obj H))) :=
  adjunctionTensorMap_eq_unit_comp _ _ _ _ G H

/-- The projection-formula map is natural in both module arguments. -/
@[reassoc]
lemma projectionFormulaMap_natural {G G' : SheafOfModules.{u} (structureRingSheaf Z)}
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (g : G ⟶ G') (k : H ⟶ H') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map ((pushforwardFunctor f).map g ×ₘ k) ≫
        projectionFormulaMap f G' H' =
      projectionFormulaMap f G H ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).map (g ×ₘ (pullbackFunctor f).map k)) :=
  adjunctionTensorMap_natural _ _ _ _ g k

/-- Tensoring the unit of `f^* ⊣ f_*` and then applying the projection-formula map is the adjoint
transpose of the pullback tensor comparison. -/
lemma projectionFormulaMap_natural_unit (F H : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map ((pullbackAdjunction f).unit.app F ×ₘ 𝟙 H) ≫
        projectionFormulaMap f ((pullbackFunctor f).obj F) H =
      (pullbackAdjunction f).homEquiv _ _ ((comparisonNatTrans f).app (F, H)) :=
  adjunctionTensorMap_unit _ _ _ _ F H

end Map

/-! ### Invertibility for a closed quotient morphism -/

section ClosedQuotient

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The unit of `f^* ⊣ f_*` at `f_*𝒢 ⊗ ℋ` is an isomorphism: by the essential-image half of
[Stacks, Tag 08KS] it suffices that the kernel ideal annihilate `f_*𝒢 ⊗ ℋ`, and it does because
it annihilates the left factor — the scalars of `f_*𝒢` act through `f^♯`, which is the forward
half of the same tag. -/
theorem isIso_unit_app_tensorSheaf (G : SheafOfModules.{u} (structureRingSheaf S.Z))
    (H : SheafOfModules.{u} (structureRingSheaf S.X)) :
    IsIso ((pullbackAdjunction S.i).unit.app
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.X.sheaf))).obj ((pushforwardFunctor S.i).obj G, H))) := by
  let : (modulePushforward S.i).Full := S.full_modulePushforward
  let : (modulePushforward S.i).Faithful := S.faithful_modulePushforward
  have hpush := (S.modulePushforward_essImage_iff ((modulePushforward S.i).obj G)).mp
    ⟨G, ⟨Iso.refl _⟩⟩
  refine (Adjunction.isIso_unit_app_iff_mem_essImage
    (modulePullbackPushforwardAdjunction S.i)).mpr ?_
  refine (S.modulePushforward_essImage_iff _).mpr ?_
  intro U a ha m
  exact smul_tensorSheaf_eq_zero ((pushforwardFunctor S.i).obj G) H U a
    (fun V hVU m => hpush V _ (S.map_mem_kernelIdeal (homOfLE hVU).op a ha) m) m

/-- **The projection formula for a closed quotient morphism of ringed spaces.**  The canonical
map `f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism.

This is a special case of [Stacks, Tag 0FZE], whose hypothesis is that `f` be affine and the two
modules quasi-coherent; no quasi-coherence is needed here. -/
theorem isIso_projectionFormulaMap (G : SheafOfModules.{u} (structureRingSheaf S.Z))
    (H : SheafOfModules.{u} (structureRingSheaf S.X)) :
    IsIso (projectionFormulaMap S.i G H) := by
  let : (pushforwardFunctor S.i).Full := S.full_modulePushforward
  let : (pushforwardFunctor S.i).Faithful := S.faithful_modulePushforward
  have hunit := isIso_unit_app_tensorSheaf S G H
  have hcounit : IsIso ((pullbackAdjunction S.i).counit.app G) :=
    isIso_counit_app (pullbackAdjunction S.i) G
  have hprod : IsIso ((pullbackAdjunction S.i).counit.app G ×ₘ
      𝟙 ((pullbackFunctor S.i).obj H)) :=
    ((asIso ((pullbackAdjunction S.i).counit.app G)).prod
      (Iso.refl ((pullbackFunctor S.i).obj H))).isIso_hom
  rw [projectionFormulaMap_eq_unit_comp]
  infer_instance

/-- **The projection formula for a closed quotient morphism of ringed spaces**, as an
isomorphism. -/
def projectionFormulaIso (G : SheafOfModules.{u} (structureRingSheaf S.Z))
    (H : SheafOfModules.{u} (structureRingSheaf S.X)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.X.sheaf))).obj ((pushforwardFunctor S.i).obj G, H) ≅
      (pushforwardFunctor S.i).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.Z.sheaf))).obj (G, (pullbackFunctor S.i).obj H)) :=
  haveI := isIso_projectionFormulaMap S G H
  asIso (projectionFormulaMap S.i G H)

/-- The forward map of the projection-formula isomorphism is the canonical adjoint transpose,
rather than an unspecified isomorphism of objects. -/
@[simp]
lemma projectionFormulaIso_hom (G : SheafOfModules.{u} (structureRingSheaf S.Z))
    (H : SheafOfModules.{u} (structureRingSheaf S.X)) :
    (projectionFormulaIso S G H).hom = projectionFormulaMap S.i G H := rfl

end ClosedQuotient

/-! ### Closed immersions of schemes -/

section Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- **The projection formula for a closed immersion of schemes**:
`i_*𝒢 ⊗_{𝒪_X} ℋ ≅ i_*(𝒢 ⊗_{𝒪_Z} i^*ℋ)`, with no quasi-coherence hypothesis.

This is a special case of [Stacks, Tag 0FZE], which states the formula for an affine morphism and
quasi-coherent modules; a closed immersion is affine, so this is the instance of that remark at a
closed immersion. -/
def closedImmersionProjectionFormulaIso
    (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
    (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).obj
        ((pushforwardFunctor i.toLRSHom.toShHom).obj G, H) ≅
      (pushforwardFunctor i.toLRSHom.toShHom).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf))).obj
          (G, (pullbackFunctor i.toLRSHom.toShHom).obj H)) :=
  projectionFormulaIso (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) G H

/-- The forward map of the closed-immersion projection formula is the canonical adjoint
transpose. -/
@[simp]
lemma closedImmersionProjectionFormulaIso_hom
    (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
    (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    (closedImmersionProjectionFormulaIso i G H).hom =
      projectionFormulaMap i.toLRSHom.toShHom G H := rfl

/-- Compatibility of the closed-immersion projection formula with the tensorized unit. -/
lemma closedImmersionProjectionFormulaIso_hom_natural_unit
    (F H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
          ((pullbackAdjunction i.toLRSHom.toShHom).unit.app F ×ₘ 𝟙 H) ≫
        (closedImmersionProjectionFormulaIso i
          ((pullbackFunctor i.toLRSHom.toShHom).obj F) H).hom =
      (pullbackAdjunction i.toLRSHom.toShHom).homEquiv _ _
        ((comparisonNatTrans i.toLRSHom.toShHom).app (F, H)) :=
  projectionFormulaMap_natural_unit i.toLRSHom.toShHom F H

end Scheme

end Stacks.AffineProjectionFormula

end
