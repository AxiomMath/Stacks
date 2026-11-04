module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SingleComparisonComposition

/-!
# The derived counit at a single complex is the ordinary counit

Let `f : X ⟶ Y` be a morphism of ringed spaces and `M` a sheaf of `𝒪_X`-modules.  There is a
canonical comparison `(f_*M)[-d] ⟶ Rf_*(M[-d])`, and this file proves that the counit of the
derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W], read through it and through the
comparison `Lf^*(N[-d]) ⟶ (f^*N)[-d]` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle`, is the ordinary
counit `f^*f_*M ⟶ M` of [Stacks, Tag 0096] placed in degree `d`.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.singlePushforwardComparison`: the canonical
  comparison `(f_*M)[-d] ⟶ Rf_*(M[-d])`, built from
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` and the two
  identifications of the single functors.
* `Stacks.SingleComparison.singleRightComparison`: the same comparison for abstract functors.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.singleMapHomologicalComplex_counit`: for an
  adjunction `G ⊣ F` of additive functors, the counit of the induced adjunction on complexes,
  read through the two single-functor identifications, is the original counit in degree `j`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_counit`: the
  same in the homotopy category.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_inv_app_eq`:
  the inverse of `Functor.mapHomotopyCategorySingleFunctor` at `M` is the image of the inverse
  of `singleMapHomologicalComplex`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedCounit_singlePushforwardComparison`:
  `Lf^*` of the comparison, followed by the derived counit, is
  `derivedToOrdinaryPullbackSingle` followed by the ordinary counit in degree `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_singlePushforwardComparison`: the
  comparison is invertible as soon as `f_* ⟶ Rf_*` is invertible at the single complex on `M`.
* `Stacks.SingleComparison.singleComparison_counit`: the counit statement for abstract functors.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-! ### The formal core of the counit identification -/

namespace Stacks.SingleComparison

universe u

section Counit

variable {AY AX KY KX DY DX : Type*} [Category AY] [Category AX] [Category KY] [Category KX]
  [Category DY] [Category DX]
  {HY : AY ⥤ KY} {HX : AX ⥤ KX} {QY : KY ⥤ DY} {QX : KX ⥤ DX}
  {PY : AY ⥤ DY} {PX : AX ⥤ DX}
  (sY : PY ≅ HY ⋙ QY) (sX : PX ≅ HX ⋙ QX)
  {l : AY ⥤ AX} {r : AX ⥤ AY} {kl : KY ⥤ KX} {kr : KX ⥤ KY}
  {L : DY ⥤ DX} {R : DX ⥤ DY}
  (adj0 : l ⊣ r) (adjK : kl ⊣ kr) (adj : L ⊣ R)
  (eL : QY ⋙ L ⟶ kl ⋙ QX) (nR : kr ⋙ QY ⟶ QX ⋙ R)
  (ml : HY ⋙ kl ≅ l ⋙ HX) (mr : HX ⋙ kr ≅ r ⋙ HY)

/-- The canonical comparison `(r M)[-d] ⟶ R(M[-d])`, abstractly: the comparison `nR` of `R`
with the "homotopy" level at the single complex on `M`, read through the two identifications of
the single functors. -/
def singleRightComparison (M : AX) : PY.obj (r.obj M) ⟶ R.obj (PX.obj M) :=
  sY.hom.app (r.obj M) ≫ QY.map (mr.inv.app M) ≫ nR.app (HX.obj M) ≫ R.map (sX.inv.app M)

/-- `singleRightComparison` is the composite of its four factors. -/
theorem singleRightComparison_eq (M : AX) :
    singleRightComparison sY sX nR mr M =
      sY.hom.app (r.obj M) ≫ QY.map (mr.inv.app M) ≫ nR.app (HX.obj M) ≫
        R.map (sX.inv.app M) :=
  rfl

/-- The counit at a single complex, abstractly.  Given

* `hfac`, the compatibility of the counit of `L ⊣ R` with the two comparisons and the counit of
  the "homotopy"-level adjunction, and
* `hcounit`, that the "homotopy"-level counit at a single complex is the "abelian"-level counit,

the composite `L(singleRightComparison M) ≫ counit` is the single-complex comparison
`Stacks.SingleComparison.singleComparison` at `r M` followed by the counit of `l ⊣ r` in the
degree the object sits in. -/
theorem singleComparison_counit
    (hfac : ∀ K : KX, L.map (nR.app K) ≫ adj.counit.app (QX.obj K) =
      eL.app (kr.obj K) ≫ QX.map (adjK.counit.app K))
    (hcounit : ∀ M : AX, kl.map (mr.inv.app M) ≫ adjK.counit.app (HX.obj M) =
      ml.hom.app (r.obj M) ≫ HX.map (adj0.counit.app M))
    (M : AX) :
    L.map (singleRightComparison sY sX nR mr M) ≫ adj.counit.app (PX.obj M) =
      singleComparison HY QY sY HX QX sX eL ml (r.obj M) ≫ PX.map (adj0.counit.app M) := by
  have h1 : L.map (R.map (sX.inv.app M)) ≫ adj.counit.app (PX.obj M) =
      adj.counit.app (QX.obj (HX.obj M)) ≫ sX.inv.app M := adj.counit.naturality _
  have h2 : L.map (QY.map (mr.inv.app M)) ≫ eL.app (kr.obj (HX.obj M)) =
      eL.app (HY.obj (r.obj M)) ≫ QX.map (kl.map (mr.inv.app M)) := eL.naturality _
  have h3 : QX.map (kl.map (mr.inv.app M)) ≫ QX.map (adjK.counit.app (HX.obj M)) =
      QX.map (ml.hom.app (r.obj M)) ≫ QX.map (HX.map (adj0.counit.app M)) := by
    rw [← QX.map_comp, ← QX.map_comp]
    exact congrArg QX.map (hcounit M)
  have h4 : QX.map (HX.map (adj0.counit.app M)) ≫ sX.inv.app M =
      sX.inv.app (l.obj (r.obj M)) ≫ PX.map (adj0.counit.app M) := sX.inv.naturality _
  simp only [singleRightComparison, singleComparison, Functor.map_comp, Category.assoc]
  rw [h1, reassoc_of% (hfac (HX.obj M)), reassoc_of% h2, reassoc_of% h3, h4]

end Counit

end Stacks.SingleComparison

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open DerivedCategory

universe u

/-! ### The formal core on cochain complexes -/

/-- For an adjunction `G ⊣ F` of additive functors, the counit of
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction` at a single complex, read through
the two single-functor identifications, is `G(F(M)) ⟶ M` placed in degree `j`. -/
theorem singleMapHomologicalComplex_counit {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : G ⊣ F)
    {ι : Type*} (c : ComplexShape ι) [DecidableEq ι] (j : ι) (M : A) :
    (G.mapHomologicalComplex c).map ((singleMapHomologicalComplex F c j).inv.app M) ≫
        (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction adj c).counit.app
          ((single A c j).obj M) =
      (singleMapHomologicalComplex G c j).hom.app (F.obj M) ≫
        (single A c j).map (adj.counit.app M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h : i = j
  · subst h
    have hnat : G.map (F.map (singleObjXSelf c i M).inv) ≫
          adj.counit.app (((single A c i).obj M).X i) =
        adj.counit.app M ≫ (singleObjXSelf c i M).inv :=
      adj.counit.naturality (singleObjXSelf c i M).inv
    have hcounit : ((CategoryTheory.Adjunction.mapHomologicalComplexAdjunction adj c).counit.app
        ((single A c i).obj M)).f i = adj.counit.app (((single A c i).obj M).X i) := rfl
    simp only [Functor.comp_obj, comp_f, Functor.mapHomologicalComplex_map_f, hcounit,
      singleMapHomologicalComplex_inv_app_self, singleMapHomologicalComplex_hom_app_self,
      single_map_f_self, Functor.map_comp, Category.assoc, Functor.id_obj]
    simp only [Iso.inv_hom_id_assoc]
    rw [hnat]
  · exact (isZero_single_obj_X c j M i h).eq_of_tgt _ _

/-! ### The same in the homotopy category -/

/-- The inverse of `T.mapHomotopyCategorySingleFunctor n` at `M` is the image under
`HomotopyCategory.quotient` of the inverse of `singleMapHomologicalComplex T _ n` at `M`. -/
theorem mapHomotopyCategorySingleFunctor_inv_app_eq {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] (T : C₁ ⥤ C₂) [T.Additive] (n : ℤ) (M : C₁) :
    (T.mapHomotopyCategorySingleFunctor n).inv.app M =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) n).inv.app M) := by
  have hhom := mapHomotopyCategorySingleFunctor_hom_app_eq T n M
  have key : (T.mapHomotopyCategorySingleFunctor n).hom.app M ≫
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) n).inv.app M) = 𝟙 _ := by
    rw [hhom]
    exact (((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        (Iso.hom_inv_id_app (singleMapHomologicalComplex T (ComplexShape.up ℤ) n) M))).trans
      ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map_id _)
  have hiso : (T.mapHomotopyCategorySingleFunctor n).inv.app M =
      CategoryTheory.inv ((T.mapHomotopyCategorySingleFunctor n).hom.app M) :=
    (CategoryTheory.IsIso.Iso.inv_hom ((T.mapHomotopyCategorySingleFunctor n).app M)).symm
  rw [hiso]
  exact CategoryTheory.IsIso.inv_eq_of_hom_inv_id key

variable {X Y : RingedSpace.{u, u}}

/-- The degreewise adjunction `K(f^*) ⊣ K(f_*)` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction`, read
through `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor`, has the ordinary counit
`f^*f_*M ⟶ M` as its component at a single complex. -/
theorem mapHomotopyCategorySingleFunctor_counit (f : X ⟶ Y) (d : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward f) d).inv.app M) ≫
        (homotopyPullbackPushforwardAdjunction f).counit.app
          ((HomotopyCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) d).obj M) =
      (Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d).hom.app
          ((modulePushforward f).obj M) ≫
        (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((modulePullbackPushforwardAdjunction f).counit.app M) := by
  have hgen := singleMapHomologicalComplex_counit
    (modulePullbackPushforwardAdjunction f) (ComplexShape.up ℤ) d M
  have h := congrArg
    (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)).map hgen
  simp only [Functor.map_comp] at h
  rw [mapHomotopyCategorySingleFunctor_hom_app_eq, mapHomotopyCategorySingleFunctor_inv_app_eq]
  exact h

/-! ### The comparison `(f_*M)[-d] ⟶ Rf_*(M[-d])` -/

section

attribute [local instance] HasDerivedCategory.standard

/-- The canonical comparison `(f_*M)[-d] ⟶ Rf_*(M[-d])` of a morphism of ringed spaces: the
comparison `f_* ⟶ Rf_*` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` at the single
complex on `M`, read through the identifications of the single functors with their
homotopy-category forms. -/
abbrev singlePushforwardComparison
    (f : X ⟶ Y) (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ) :
    (singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj
        ((modulePushforward f).obj M) ⟶
      (derivedPushforward f).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj M) :=
  Stacks.SingleComparison.singleRightComparison
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d)
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d)
    (derivedPushforwardUnit f)
    (Functor.mapHomotopyCategorySingleFunctor (modulePushforward f) d) M

/-- The comparison `(f_*M)[-d] ⟶ Rf_*(M[-d])` is invertible as soon as the comparison
`f_* ⟶ Rf_*` is invertible at the single complex on `M`. -/
theorem isIso_singlePushforwardComparison (f : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheafRing X)) (d : ℤ)
    (h : IsIso ((derivedPushforwardUnit f).app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) d).obj M))) :
    IsIso (singlePushforwardComparison f M d) := by
  have := h
  simp only [singlePushforwardComparison, Stacks.SingleComparison.singleRightComparison_eq]
  infer_instance

/-- The derived counit at a single complex is the ordinary counit: for a morphism of ringed
spaces `f : X ⟶ Y` and a sheaf of `𝒪_X`-modules `M`, the derived pullback of the comparison
`(f_*M)[-d] ⟶ Rf_*(M[-d])` followed by the counit of `Lf^* ⊣ Rf_*` is the comparison
`Lf^*((f_*M)[-d]) ⟶ (f^*f_*M)[-d]` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` followed by the
ordinary counit `f^*f_*M ⟶ M` in degree `d`. -/
theorem derivedCounit_singlePushforwardComparison (f : X ⟶ Y) (d : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedPullback f).map (singlePushforwardComparison f M d) ≫
        (derivedAdjunction f).counit.app
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj M) =
      derivedToOrdinaryPullbackSingle f ((modulePushforward f).obj M) d ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((modulePullbackPushforwardAdjunction f).counit.app M) :=
  Stacks.SingleComparison.singleComparison_counit
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d)
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d)
    (modulePullbackPushforwardAdjunction f)
    (homotopyPullbackPushforwardAdjunction f)
    (derivedAdjunction f)
    (derivedPullbackComparison f)
    (derivedPushforwardUnit f)
    (Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d)
    (Functor.mapHomotopyCategorySingleFunctor (modulePushforward f) d)
    (derivedAdjunction_counit_fac f)
    (mapHomotopyCategorySingleFunctor_counit f d) M

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
