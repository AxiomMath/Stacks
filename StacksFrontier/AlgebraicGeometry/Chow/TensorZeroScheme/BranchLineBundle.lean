module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchBundle
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchFibreProduct
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.TotalSpaceComparison

/-!
# Each branch of the zero scheme of a tensor product is a line bundle over `D`

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`, as in [Stacks, Tag 0F97]. The
tag's condition (4) identifies the branch `D₁` with

  `\underline{\Spec}_D(\Sym^*(L_2^{⊗ -1}|_D))`,

which is `Stacks.Chow.TensorZeroScheme.branchSituation`, and the branch `D₂` with the same
construction for `L₁`. This file proves that identification, as an isomorphism of schemes over
`D`, and shows that it carries the zero section of the line bundle to the zero section of the
branch. The branch `D₁` is identified with the fibre product `D ×_Y Tot(L₂^{⊗ -1})`, and that
fibre product with the line bundle of condition (4).

## Main definitions

* `Stacks.Chow.TensorZeroScheme.branchSituationIso`: the total space of the branch situation is
  the line bundle of `N|_D` over `D`.
* `Stacks.Chow.TensorZeroScheme.branchFibreProductLineBundleIso₁` and
  `branchFibreProductLineBundleIso₂`: the fibre products `D ×_Y Tot(L_{3-i}^{⊗ -1})` are the line
  bundles of `L_{3-i}|_D` over `D`.
* `Stacks.Chow.TensorZeroScheme.zeroSectionFibreProduct₁` and `zeroSectionFibreProduct₂`: the zero
  sections of those fibre products over `D`.
* `Stacks.Chow.TensorZeroScheme.branchBundleIso₁` and `branchBundleIso₂`: the fibre products are
  the line bundles of condition (4).
* `Stacks.Chow.TensorZeroScheme.branchIso₁` and `branchIso₂`: **the identifications of the two
  branches with the line bundles of [Stacks, Tag 0F97](4).**

## Main results

* `Stacks.Chow.TensorZeroScheme.branchIso₁_hom_comp_totalSpaceToBase` and
  `branchIso₂_hom_comp_totalSpaceToBase`: **the identifications are of schemes over `D`.**
* `Stacks.Chow.TensorZeroScheme.exists_iso_branchSituation₁` and
  `exists_iso_branchSituation₂`: **[Stacks, Tag 0F97](4)**, in the form the tag states it.
* `Stacks.Chow.TensorZeroScheme.zeroSectionFibreProduct₁_comp_branchBundleIso₁_hom` and its
  mirror: the identification carries the zero section of the fibre product to the zero section of
  the line bundle of condition (4).

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

/-! ### The line bundle of condition (4) is the line bundle of the restricted module -/

variable (N : Y.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]

include h₁ h₂ hN in
/-- **The module of the branch situation is the inverse of the restricted module**: the
restriction `(N^{⊗ -1})|_D` of the inverse is the inverse `(N|_D)^{⊗ -1}` of the restriction. -/
def branchSituationModuleIso :
    (branchSituation Y L₁ L₂ s N).L ≅
      (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)).L :=
  Stacks.LineBundle.inverseSituationPullbackIso (zeroIdeal Y L₁ L₂ s).subschemeι N

include h₁ h₂ hN in
/-- The inverse of the restricted module is invertible, read on the base of the branch
situation. -/
theorem isInvertible_branchSituationBase :
    AlgebraicGeometry.SheafOfModules.IsInvertible (branchSituation Y L₁ L₂ s N).X.sheaf.obj
      (branchSituation Y L₁ L₂ s N).X.ringCatSheaf.property
      (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)).L :=
  Stacks.LineBundle.Situation.invertible
    (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N))

include h₁ h₂ hN in
/-- **The total space of the branch situation is the line bundle of `N|_D` over `D`.** -/
def branchSituationIso :
    Stacks.LineBundle.lineBundleSpace (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) ≅
      (branchSituation Y L₁ L₂ s N).totalSpace :=
  haveI := isInvertible_branchSituationBase Y L₁ L₂ s N
  (branchSituation Y L₁ L₂ s N).totalSpaceIsoOfIso
    (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)).L
    (branchSituationModuleIso Y L₁ L₂ s N)

include h₁ h₂ hN in
/-- The identification of the branch situation with the line bundle of `N|_D` is one of schemes
over `D`. -/
theorem branchSituationIso_hom_comp_totalSpaceToBase :
    (branchSituationIso Y L₁ L₂ s N).hom ≫ (branchSituation Y L₁ L₂ s N).totalSpaceToBase =
      Stacks.LineBundle.lineBundleProj (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N) :=
  have := isInvertible_branchSituationBase Y L₁ L₂ s N
  (branchSituation Y L₁ L₂ s N).totalSpaceIsoOfIso_hom_comp_totalSpaceToBase _
    (branchSituationModuleIso Y L₁ L₂ s N)

include h₁ h₂ hN in
/-- The identification of the branch situation with the line bundle of `N|_D` carries the zero
section to the zero section. -/
theorem zeroSection_comp_branchSituationIso_hom :
    (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
          ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj N)).zeroSection ≫
        (branchSituationIso Y L₁ L₂ s N).hom = (branchSituation Y L₁ L₂ s N).zeroSection :=
  have := isInvertible_branchSituationBase Y L₁ L₂ s N
  (branchSituation Y L₁ L₂ s N).zeroSection_comp_totalSpaceIsoOfIso_hom _
    (branchSituationModuleIso Y L₁ L₂ s N)

/-! ### The fibre products are the line bundles of the restricted modules -/

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₂^{⊗ -1})` is the line bundle of `L₂|_D` over `D`.** -/
def branchFibreProductLineBundleIso₁ :
    Stacks.LineBundle.lineBundleSpace (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂) ≅
      branchFibreProduct₁ Y L₁ L₂ s :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₂).flip.isoPullback

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₁^{⊗ -1})` is the line bundle of `L₁|_D` over `D`.** -/
def branchFibreProductLineBundleIso₂ :
    Stacks.LineBundle.lineBundleSpace (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁) ≅
      branchFibreProduct₂ Y L₁ L₂ s :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₁).flip.isoPullback

include h₁ h₂ in
/-- The identification of `D ×_Y Tot(L₂^{⊗ -1})` with the line bundle of `L₂|_D` is one of
schemes over `D`. -/
theorem branchFibreProductLineBundleIso₁_hom_comp_base :
    (branchFibreProductLineBundleIso₁ Y L₁ L₂ s).hom ≫ branchFibreProductToBase₁ Y L₁ L₂ s =
      Stacks.LineBundle.lineBundleProj (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂) :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₂).flip.isoPullback_hom_fst

include h₁ h₂ in
/-- The identification of `D ×_Y Tot(L₁^{⊗ -1})` with the line bundle of `L₁|_D` is one of
schemes over `D`. -/
theorem branchFibreProductLineBundleIso₂_hom_comp_base :
    (branchFibreProductLineBundleIso₂ Y L₁ L₂ s).hom ≫ branchFibreProductToBase₂ Y L₁ L₂ s =
      Stacks.LineBundle.lineBundleProj (zeroIdeal Y L₁ L₂ s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁) :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₁).flip.isoPullback_hom_fst

include h₁ h₂ in
/-- The line-bundle coordinate of the identification of `D ×_Y Tot(L₂^{⊗ -1})` is the canonical
morphism of total spaces along `i`. -/
theorem branchFibreProductLineBundleIso₁_hom_comp_fibre :
    (branchFibreProductLineBundleIso₁ Y L₁ L₂ s).hom ≫ branchFibreProductToFibre₁ Y L₁ L₂ s =
      Stacks.LineBundle.totalSpaceBaseChange (zeroIdeal Y L₁ L₂ s).subschemeι L₂ :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₂).flip.isoPullback_hom_snd

include h₁ h₂ in
/-- The line-bundle coordinate of the identification of `D ×_Y Tot(L₁^{⊗ -1})` is the canonical
morphism of total spaces along `i`. -/
theorem branchFibreProductLineBundleIso₂_hom_comp_fibre :
    (branchFibreProductLineBundleIso₂ Y L₁ L₂ s).hom ≫ branchFibreProductToFibre₂ Y L₁ L₂ s =
      Stacks.LineBundle.totalSpaceBaseChange (zeroIdeal Y L₁ L₂ s).subschemeι L₁ :=
  (Stacks.LineBundle.isPullback_totalSpaceBaseChange
    (zeroIdeal Y L₁ L₂ s).subschemeι L₁).flip.isoPullback_hom_snd

/-! ### The zero sections of the fibre products -/

/-- Restricting along `i : D ⟶ Y` and then taking the zero section of a line bundle over `Y`
projects back to `i`. -/
private theorem zeroSection_condition {D : Scheme.{u}} (i : D ⟶ Y) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    CategoryTheory.CategoryStruct.id D ≫ i =
      (i ≫ (Stacks.LineBundle.inverseSituation Y M).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y M :=
  (Category.id_comp i).trans
    (Eq.symm ((Category.assoc _ _ _).trans
      ((congrArg (fun z : Y ⟶ Y => i ≫ z)
          (Stacks.LineBundle.inverseSituation Y M).zeroSection_comp_totalSpaceToBase).trans
        (Category.comp_id i))))

include h₁ h₂ in
/-- The defining square of the zero section of `D ×_Y Tot(L₂^{⊗ -1})`. -/
theorem zeroSectionFibreProduct₁_condition :
    CategoryTheory.CategoryStruct.id (zeroIdeal Y L₁ L₂ s).subscheme ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι =
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫
          (Stacks.LineBundle.inverseSituation Y L₂).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y L₂ :=
  zeroSection_condition Y _ _

include h₁ h₂ in
/-- The defining square of the zero section of `D ×_Y Tot(L₁^{⊗ -1})`. -/
theorem zeroSectionFibreProduct₂_condition :
    CategoryTheory.CategoryStruct.id (zeroIdeal Y L₁ L₂ s).subscheme ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι =
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫
          (Stacks.LineBundle.inverseSituation Y L₁).zeroSection) ≫
        Stacks.LineBundle.lineBundleProj Y L₁ :=
  zeroSection_condition Y _ _

include h₁ h₂ in
/-- **The zero section of `D ×_Y Tot(L₂^{⊗ -1})` over `D`**: the identity in the first coordinate
and the zero section of the second line bundle in the second. -/
def zeroSectionFibreProduct₁ :
    (zeroIdeal Y L₁ L₂ s).subscheme ⟶ branchFibreProduct₁ Y L₁ L₂ s :=
  Limits.pullback.lift (CategoryTheory.CategoryStruct.id _)
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ (Stacks.LineBundle.inverseSituation Y L₂).zeroSection)
    (zeroSectionFibreProduct₁_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- **The zero section of `D ×_Y Tot(L₁^{⊗ -1})` over `D`.** -/
def zeroSectionFibreProduct₂ :
    (zeroIdeal Y L₁ L₂ s).subscheme ⟶ branchFibreProduct₂ Y L₁ L₂ s :=
  Limits.pullback.lift (CategoryTheory.CategoryStruct.id _)
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ (Stacks.LineBundle.inverseSituation Y L₁).zeroSection)
    (zeroSectionFibreProduct₂_condition Y L₁ L₂ s)

include h₁ h₂ in
/-- The zero section of `D ×_Y Tot(L₂^{⊗ -1})` is a section of the projection to `D`. -/
theorem zeroSectionFibreProduct₁_comp_base :
    zeroSectionFibreProduct₁ Y L₁ L₂ s ≫ branchFibreProductToBase₁ Y L₁ L₂ s =
      CategoryTheory.CategoryStruct.id _ :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The zero section of `D ×_Y Tot(L₁^{⊗ -1})` is a section of the projection to `D`. -/
theorem zeroSectionFibreProduct₂_comp_base :
    zeroSectionFibreProduct₂ Y L₁ L₂ s ≫ branchFibreProductToBase₂ Y L₁ L₂ s =
      CategoryTheory.CategoryStruct.id _ :=
  Limits.pullback.lift_fst _ _ _

include h₁ h₂ in
/-- The line-bundle coordinate of the zero section of `D ×_Y Tot(L₂^{⊗ -1})` is the zero section
of the second line bundle. -/
theorem zeroSectionFibreProduct₁_comp_fibre :
    zeroSectionFibreProduct₁ Y L₁ L₂ s ≫ branchFibreProductToFibre₁ Y L₁ L₂ s =
      (zeroIdeal Y L₁ L₂ s).subschemeι ≫ (Stacks.LineBundle.inverseSituation Y L₂).zeroSection :=
  Limits.pullback.lift_snd _ _ _

include h₁ h₂ in
/-- The line-bundle coordinate of the zero section of `D ×_Y Tot(L₁^{⊗ -1})` is the zero section
of the first line bundle. -/
theorem zeroSectionFibreProduct₂_comp_fibre :
    zeroSectionFibreProduct₂ Y L₁ L₂ s ≫ branchFibreProductToFibre₂ Y L₁ L₂ s =
      (zeroIdeal Y L₁ L₂ s).subschemeι ≫ (Stacks.LineBundle.inverseSituation Y L₁).zeroSection :=
  Limits.pullback.lift_snd _ _ _

/-- If `f ≫ p = q` and `c ≫ q = r`, then `(c ≫ f) ≫ p = r`. -/
private theorem comp_eq_of_comp_eq {W V T A : Scheme.{u}} (c : W ⟶ V) (f : V ⟶ T) (p : T ⟶ A)
    (q : V ⟶ A) (r : W ⟶ A) (h : f ≫ p = q) (hr : c ≫ q = r) : (c ≫ f) ≫ p = r :=
  (Category.assoc c f p).trans ((congrArg (fun z : V ⟶ A => c ≫ z) h).trans hr)

include h₁ h₂ in
/-- **The identification of `D ×_Y Tot(L₂^{⊗ -1})` with the line bundle of `L₂|_D` carries the
zero section to the zero section.** -/
theorem zeroSection_comp_branchFibreProductLineBundleIso₁_hom :
    (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
          ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂)).zeroSection ≫
        (branchFibreProductLineBundleIso₁ Y L₁ L₂ s).hom = zeroSectionFibreProduct₁ Y L₁ L₂ s := by
  refine branchFibreProduct₁_hom_ext Y L₁ L₂ s ?_ ?_
  · exact (comp_eq_of_comp_eq _ _ _ _ _
      (branchFibreProductLineBundleIso₁_hom_comp_base Y L₁ L₂ s)
      (Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceToBase _)).trans
      (zeroSectionFibreProduct₁_comp_base Y L₁ L₂ s).symm
  · exact (comp_eq_of_comp_eq _ _ _ _ _
      (branchFibreProductLineBundleIso₁_hom_comp_fibre Y L₁ L₂ s)
      (Stacks.LineBundle.zeroSection_comp_totalSpaceBaseChange _ _)).trans
      (zeroSectionFibreProduct₁_comp_fibre Y L₁ L₂ s).symm

include h₁ h₂ in
/-- **The identification of `D ×_Y Tot(L₁^{⊗ -1})` with the line bundle of `L₁|_D` carries the
zero section to the zero section.** -/
theorem zeroSection_comp_branchFibreProductLineBundleIso₂_hom :
    (Stacks.LineBundle.inverseSituation (zeroIdeal Y L₁ L₂ s).subscheme
          ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁)).zeroSection ≫
        (branchFibreProductLineBundleIso₂ Y L₁ L₂ s).hom = zeroSectionFibreProduct₂ Y L₁ L₂ s := by
  refine branchFibreProduct₂_hom_ext Y L₁ L₂ s ?_ ?_
  · exact (comp_eq_of_comp_eq _ _ _ _ _
      (branchFibreProductLineBundleIso₂_hom_comp_base Y L₁ L₂ s)
      (Stacks.LineBundle.Situation.zeroSection_comp_totalSpaceToBase _)).trans
      (zeroSectionFibreProduct₂_comp_base Y L₁ L₂ s).symm
  · exact (comp_eq_of_comp_eq _ _ _ _ _
      (branchFibreProductLineBundleIso₂_hom_comp_fibre Y L₁ L₂ s)
      (Stacks.LineBundle.zeroSection_comp_totalSpaceBaseChange _ _)).trans
      (zeroSectionFibreProduct₂_comp_fibre Y L₁ L₂ s).symm

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₂^{⊗ -1})` is the line bundle of [Stacks, Tag 0F97](4) for
the first branch.** -/
def branchBundleIso₁ :
    branchFibreProduct₁ Y L₁ L₂ s ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace :=
  (branchFibreProductLineBundleIso₁ Y L₁ L₂ s).symm ≪≫ branchSituationIso Y L₁ L₂ s L₂

include h₁ h₂ in
/-- **The fibre product `D ×_Y Tot(L₁^{⊗ -1})` is the line bundle of [Stacks, Tag 0F97](4) for
the second branch.** -/
def branchBundleIso₂ :
    branchFibreProduct₂ Y L₁ L₂ s ≅ (branchSituation Y L₁ L₂ s L₁).totalSpace :=
  (branchFibreProductLineBundleIso₂ Y L₁ L₂ s).symm ≪≫ branchSituationIso Y L₁ L₂ s L₁

include h₁ h₂ in
/-- The identification of `D ×_Y Tot(L₂^{⊗ -1})` with the line bundle of condition (4) is one of
schemes over `D`. -/
theorem branchBundleIso₁_hom_comp_totalSpaceToBase :
    (branchBundleIso₁ Y L₁ L₂ s).hom ≫ (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase =
      branchFibreProductToBase₁ Y L₁ L₂ s :=
  comp_eq_of_comp_eq (branchFibreProductLineBundleIso₁ Y L₁ L₂ s).inv
    (branchSituationIso Y L₁ L₂ s L₂).hom (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase
    (Stacks.LineBundle.lineBundleProj (zeroIdeal Y L₁ L₂ s).subscheme
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
    (branchFibreProductToBase₁ Y L₁ L₂ s)
    (branchSituationIso_hom_comp_totalSpaceToBase Y L₁ L₂ s L₂)
    ((Iso.inv_comp_eq _).mpr (branchFibreProductLineBundleIso₁_hom_comp_base Y L₁ L₂ s).symm)

include h₁ h₂ in
/-- The identification of `D ×_Y Tot(L₁^{⊗ -1})` with the line bundle of condition (4) is one of
schemes over `D`. -/
theorem branchBundleIso₂_hom_comp_totalSpaceToBase :
    (branchBundleIso₂ Y L₁ L₂ s).hom ≫ (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase =
      branchFibreProductToBase₂ Y L₁ L₂ s :=
  comp_eq_of_comp_eq (branchFibreProductLineBundleIso₂ Y L₁ L₂ s).inv
    (branchSituationIso Y L₁ L₂ s L₁).hom (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase
    (Stacks.LineBundle.lineBundleProj (zeroIdeal Y L₁ L₂ s).subscheme
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₁))
    (branchFibreProductToBase₂ Y L₁ L₂ s)
    (branchSituationIso_hom_comp_totalSpaceToBase Y L₁ L₂ s L₁)
    ((Iso.inv_comp_eq _).mpr (branchFibreProductLineBundleIso₂_hom_comp_base Y L₁ L₂ s).symm)

/-- Transporting along `e.symm ≪≫ f` the zero section `z ≫ e.hom` gives `z ≫ f.hom`. -/
private theorem comp_symm_trans_hom_eq {A B C E : Scheme.{u}} {z : A ⟶ B} {w : A ⟶ C} {t : A ⟶ E}
    {e : B ≅ C} (f : B ≅ E) (h : z ≫ e.hom = w) (hf : z ≫ f.hom = t) :
    w ≫ (e.symm ≪≫ f).hom = t := by
  rw [← h, Category.assoc, Iso.trans_hom, Iso.symm_hom, e.hom_inv_id_assoc, hf]

include h₁ h₂ in
/-- **The identification of `D ×_Y Tot(L₂^{⊗ -1})` with the line bundle of condition (4) carries
the zero section to the zero section.** -/
theorem zeroSectionFibreProduct₁_comp_branchBundleIso₁_hom :
    zeroSectionFibreProduct₁ Y L₁ L₂ s ≫ (branchBundleIso₁ Y L₁ L₂ s).hom =
      (branchSituation Y L₁ L₂ s L₂).zeroSection :=
  comp_symm_trans_hom_eq _
    (zeroSection_comp_branchFibreProductLineBundleIso₁_hom Y L₁ L₂ s)
    (zeroSection_comp_branchSituationIso_hom Y L₁ L₂ s L₂)

include h₁ h₂ in
/-- **The identification of `D ×_Y Tot(L₁^{⊗ -1})` with the line bundle of condition (4) carries
the zero section to the zero section.** -/
theorem zeroSectionFibreProduct₂_comp_branchBundleIso₂_hom :
    zeroSectionFibreProduct₂ Y L₁ L₂ s ≫ (branchBundleIso₂ Y L₁ L₂ s).hom =
      (branchSituation Y L₁ L₂ s L₁).zeroSection :=
  comp_symm_trans_hom_eq _
    (zeroSection_comp_branchFibreProductLineBundleIso₂_hom Y L₁ L₂ s)
    (zeroSection_comp_branchSituationIso_hom Y L₁ L₂ s L₁)

/-! ### Condition (4) -/

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the first branch**: `D₁` is the line bundle
`\underline{\Spec}_D(\Sym^*(L₂^{⊗ -1}|_D))`. -/
def branchIso₁ :
    (branch₁ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace :=
  asIso (branchToFibreProduct₁ Y L₁ L₂ s) ≪≫ branchBundleIso₁ Y L₁ L₂ s

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the second branch**: `D₂` is the line bundle
`\underline{\Spec}_D(\Sym^*(L₁^{⊗ -1}|_D))`. -/
def branchIso₂ :
    (branch₂ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₁).totalSpace :=
  asIso (branchToFibreProduct₂ Y L₁ L₂ s) ≪≫ branchBundleIso₂ Y L₁ L₂ s

include h₁ h₂ in
/-- The identification of the first branch, read through the comparison with the fibre
product. -/
theorem branchIso₁_hom :
    (branchIso₁ Y L₁ L₂ s).hom =
      branchToFibreProduct₁ Y L₁ L₂ s ≫ (branchBundleIso₁ Y L₁ L₂ s).hom :=
  rfl

include h₁ h₂ in
/-- The identification of the second branch, read through the comparison with the fibre
product. -/
theorem branchIso₂_hom :
    (branchIso₂ Y L₁ L₂ s).hom =
      branchToFibreProduct₂ Y L₁ L₂ s ≫ (branchBundleIso₂ Y L₁ L₂ s).hom :=
  rfl

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the first branch, the compatibility over `D`.** -/
theorem branchIso₁_hom_comp_totalSpaceToBase :
    (branchIso₁ Y L₁ L₂ s).hom ≫ (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase =
      proj₁ Y L₁ L₂ s :=
  comp_eq_of_comp_eq (branchToFibreProduct₁ Y L₁ L₂ s) (branchBundleIso₁ Y L₁ L₂ s).hom
    (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase (branchFibreProductToBase₁ Y L₁ L₂ s)
    (proj₁ Y L₁ L₂ s) (branchBundleIso₁_hom_comp_totalSpaceToBase Y L₁ L₂ s)
    (branchToFibreProduct₁_comp_base Y L₁ L₂ s)

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the second branch, the compatibility over `D`.** -/
theorem branchIso₂_hom_comp_totalSpaceToBase :
    (branchIso₂ Y L₁ L₂ s).hom ≫ (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase =
      proj₂ Y L₁ L₂ s :=
  comp_eq_of_comp_eq (branchToFibreProduct₂ Y L₁ L₂ s) (branchBundleIso₂ Y L₁ L₂ s).hom
    (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase (branchFibreProductToBase₂ Y L₁ L₂ s)
    (proj₂ Y L₁ L₂ s) (branchBundleIso₂_hom_comp_totalSpaceToBase Y L₁ L₂ s)
    (branchToFibreProduct₂_comp_base Y L₁ L₂ s)

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the first branch**, in the form the tag states it: `D₁` is the
line bundle `\underline{\Spec}_D(\Sym^*(L₂^{⊗ -1}|_D))` over `D`. -/
theorem exists_iso_branchSituation₁ :
    ∃ e : (branch₁ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace,
      e.hom ≫ (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase = proj₁ Y L₁ L₂ s :=
  ⟨branchIso₁ Y L₁ L₂ s, branchIso₁_hom_comp_totalSpaceToBase Y L₁ L₂ s⟩

include h₁ h₂ in
/-- **[Stacks, Tag 0F97](4) for the second branch**, in the form the tag states it: `D₂` is the
line bundle `\underline{\Spec}_D(\Sym^*(L₁^{⊗ -1}|_D))` over `D`. -/
theorem exists_iso_branchSituation₂ :
    ∃ e : (branch₂ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₁).totalSpace,
      e.hom ≫ (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase = proj₂ Y L₁ L₂ s :=
  ⟨branchIso₂ Y L₁ L₂ s, branchIso₂_hom_comp_totalSpaceToBase Y L₁ L₂ s⟩

end Stacks.Chow.TensorZeroScheme

end
