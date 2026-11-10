module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.MoreLocalization
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Abelian sheaves on a localized site: inverse image, direct image, and K-injectives

Let `(C, J)` be a site and `f : U ⟶ V` a morphism of `C`. Composing with `f` is a functor
`Over.map f : Over U ⥤ Over V`, continuous and cocontinuous for the localized topologies, so it
induces an adjoint pair on abelian sheaves: the inverse image `f^{-1} : Ab(C/V) ⥤ Ab(C/U)` and
the direct image `f_* : Ab(C/U) ⥤ Ab(C/V)`. This file sets up that pair and proves the two
facts about it on which the base change statement of Stacks 0EZ0 rests.

The first is that `f^{-1}` carries K-injective complexes to K-injective complexes. By the
adjoint criterion for K-injectivity (Stacks 08BJ) it suffices that `f^{-1}` have an exact left
adjoint. That left adjoint is the sheafified left Kan extension along `(Over.map f).op`, and its
left exactness is the point needing an argument: the Kan extension evaluated at `V' : Over V` is
a colimit over `CostructuredArrow (Over.map f).op (op V')`, and that index category admits a
*final* discrete subcategory, namely the set of liftings `{g : V'.left ⟶ U // g ≫ f = V'.hom}`
of `V'` through `f`. Exactness of colimits over a discrete category is Grothendieck's axiom AB4
for abelian groups, and finality transports that exactness to the whole index category.

The second is that abelian sheaves on a site form a Grothendieck abelian category, obtained by
transporting the statement along the equivalence of the site with a small model of itself.

## Main definitions

* `Stacks.Cohomology.Localization.AbelianSheaves`: abelian sheaves on the localization of a site
  at an object.
* `Stacks.Cohomology.Localization.overPullback`, `.overPushforward`: the inverse and direct
  image between localized sites induced by a morphism of the underlying site.
* `Stacks.Cohomology.Localization.homotopyToDerived`: an additive functor applied degreewise on
  the homotopy category, followed by passage to the derived category of its target.

## Main results

* `Stacks.Cohomology.Localization.sheaf_isGrothendieckAbelian`: abelian sheaves on a site form a
  Grothendieck abelian category.
* `Stacks.Cohomology.Localization.overPullback_map_isKInjective`: the inverse image between
  localized sites preserves K-injective complexes of abelian sheaves.
* `Stacks.Cohomology.Localization.preservesFiniteLimits_overMap_op_lan`: the left exactness of
  the left Kan extension along `(Over.map f).op`, for abelian groups in any universe dominating
  that of the site.

## Implementation notes

The site has independent object and morphism universes `u` and `v`, and the abelian groups live
in `max u v`, which is the universe in which the pointwise left Kan extensions defining the
direct image exist for an arbitrary universe-polymorphic site.

The left exactness of the Kan extension is proved for abelian groups in any universe `w` with
`UnivLE.{max u v, w}`, not only `w = max u v`: the index type of the final discrete subcategory
lives in `Type v` and is transported into `Type w` before AB4 is applied, exactly as in
`costructuredArrow_hasExactColimitsOfShape`. That generality is what a site whose objects form a
`Type (u + 1)` with morphisms in `Type u` and whose coefficients are `Ab.{max (u + 1) v}` needs,
and it is exported as the single public `preservesFiniteLimits_overMap_op_lan`; the three
declarations carrying the argument stay `private`.

The finality argument is packaged as an adjunction `overMapLiftProjection ⊣ overMapLiftInclusion`
between the discrete category of liftings and the costructured-arrow category rather than as a
bare cofinality check, because the unit and counit are what identify the colimit over the
liftings with the Kan extension; `hasExactColimitsOfShape_of_final` then needs only the formal
consequence that a left adjoint is final.

The naturality square of `overMapLanEvaluationIsoColim` is reassociated once more after
`Functor.lan` and `Functor.lanUnit` are unfolded: unfolding them regroups the composite, so the
rewrite by the colimit comparison no longer matches, and a second `Category.assoc` pass restores
the shape that rewrite expects.

`overPushforward_additive` overlaps
`Stacks.ComparingTopologies.sheafPushforwardCocontinuous_additive`, which is the same statement
for a small site; the form here has independent object and morphism universes and subsumes it.

## References

* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w
universe uA vA wDA uB vB wDB wG uC vC wDC wU wX wV' wY

namespace Stacks.Cohomology.Localization

/-- Applying an additive functor degreewise on the homotopy category and then passing to the
derived category of its target. -/
abbrev homotopyToDerived {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Abelian sheaves on a site form a Grothendieck abelian category: the site is equivalent to a
small model of itself, and the statement is transported along that equivalence. It is an
instance, so that injective resolutions of abelian sheaves on a site whose objects live in a
larger universe than its morphisms, such as a big site of schemes, are found automatically. -/
instance (priority := 50) sheaf_isGrothendieckAbelian
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{max u v}] :
    IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (Sheaf J Ab.{max u v}) := by
  let e := equivSmallModel.{max u v} C
  let K := e.inverse.inducedTopology J
  have : HasSheafify K Ab.{max u v} :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K e.functor
  let : IsGrothendieckAbelian.{max u v, max u v, max u v + 1} Ab.{max u v} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u v, max u v, v, max u v + 1, u}
    (J := J) (A := Ab.{max u v})

/-- On a Grothendieck abelian category, the additive functor `F` applied on the homotopy category
and followed by `Qh` has a pointwise right derived functor along quasi-isomorphisms. -/
private lemma hasPointwiseRightDerivedFunctor_homotopyToDerived
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [IsGrothendieckAbelian.{wG, vA, uA} A] (F : A ⥤ B) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
    vA, wDB, wDA, uA, max uB vB, max uA vA} _
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)).1

private noncomputable def rightDerivedOfGrothendieck
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [IsGrothendieckAbelian.{wG, vA, uA} A] (F : A ⥤ B) [F.Additive] :
    DerivedCategory A ⥤ DerivedCategory B := by
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have := hasPointwiseRightDerivedFunctor_homotopyToDerived F
  exact Fh.totalRightDerived DerivedCategory.Qh W

private noncomputable def rightDerivedOfGrothendieckUnit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [IsGrothendieckAbelian.{wG, vA, uA} A] (F : A ⥤ B) [F.Additive] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ rightDerivedOfGrothendieck F := by
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have := hasPointwiseRightDerivedFunctor_homotopyToDerived F
  exact Fh.totalRightDerivedUnit DerivedCategory.Qh W

private lemma rightDerivedOfGrothendieck_isRightDerived
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [IsGrothendieckAbelian.{wG, vA, uA} A] (F : A ⥤ B) [F.Additive] :
    (rightDerivedOfGrothendieck F).IsRightDerivedFunctor
      (rightDerivedOfGrothendieckUnit F)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  have := hasPointwiseRightDerivedFunctor_homotopyToDerived F
  dsimp [rightDerivedOfGrothendieck, rightDerivedOfGrothendieckUnit]
  infer_instance

/-- Let `RF` be a right derived functor of `F` along quasi-isomorphisms, with unit `α`, on a
Grothendieck abelian category. Then the component of `α` at a K-injective complex `I` is an
isomorphism. -/
lemma rightDerivedUnit_isIso_app_of_isKInjective
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wDA} A]
    [IsGrothendieckAbelian.{wG, vA, uA} A]
    {H : Type uB} [Category.{vB} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory A ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)).2
    DerivedCategory.Qh RF α I hI

private noncomputable def exactDerivedFunctorIso
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    (F : A ⥤ B) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    F.mapDerivedCategory ≅ RF := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  exact Functor.rightDerivedUnique _ _ F.mapDerivedCategoryFactorsh.inv α W

/-- If `F` is an exact additive functor, then the unit `α` of any right derived functor `RF` of
`F` along quasi-isomorphisms is an isomorphism. -/
lemma exactRightDerivedUnit_isIso
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Abelian A]
    [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    (F : A ⥤ B) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    IsIso α := by
  let e := exactDerivedFunctorIso F RF α
  have he : F.mapDerivedCategoryFactorsh.inv ≫
      Functor.whiskerLeft DerivedCategory.Qh e.hom = α := by
    dsimp [e, exactDerivedFunctorIso]
    simp
  rw [← he]
  infer_instance

private lemma isIso_natTrans_of_isIso_app_on_kInjectives
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wDA} A]
    {H : Type uB} [Category.{vB} H] {F G : DerivedCategory A ⥤ H}
    (τ : F ⟶ G)
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f)
    (hτ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (τ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A
        (ComplexShape.up ℤ)).obj I)))) : IsIso τ := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let K := DerivedCategory.Qh.objPreimage X
  obtain ⟨I, f, hI, hf⟩ := hres K.as
  have hfq : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  have hQ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) :=
    Localization.inverts DerivedCategory.Qh _ _ hfq
  have hpre : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≅ X :=
    (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))).symm ≪≫
      DerivedCategory.Qh.objObjPreimageIso X
  exact (NatTrans.isIso_app_iff_of_iso τ hpre).mp (hτ I hI)

/-- The natural transformation from `F ⋙ G` on the homotopy category to `RF ⋙ RG` on the
derived category obtained by composing the units `αF` and `αG`. -/
noncomputable def derivedCompositeUnit
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Abelian A] [Category.{vB} B] [Abelian B]
    [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [HasDerivedCategory.{wDC} C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory B ⥤ DerivedCategory C)
    (αF : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RG) :
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RF ⋙ RG := by
  let e := Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  exact (Functor.isoWhiskerRight e.symm DerivedCategory.Qh).hom ≫
    (Functor.associator Fh Gh DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft Fh αG ≫
    (Functor.associator Fh DerivedCategory.Qh RG).inv ≫
    Functor.whiskerRight αF RG ≫
    (Functor.associator DerivedCategory.Qh RF RG).hom

/-- If the composite unit `derivedCompositeUnit F G RF RG αF αG` is an isomorphism at every
K-injective complex, then `RF ⋙ RG` is the right derived functor of `F ⋙ G` along
quasi-isomorphisms. -/
lemma derivedComposite_isRightDerived
    {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Abelian A] [Category.{vB} B] [Abelian B]
    [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{wDA} A] [HasDerivedCategory.{wDB} B]
    [HasDerivedCategory.{wDC} C]
    [IsGrothendieckAbelian.{wG, vA, uA} A]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory B ⥤ DerivedCategory C)
    (αF : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    (hβ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso ((derivedCompositeUnit F G RF RG αF αG).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    (RF ⋙ RG).IsRightDerivedFunctor (derivedCompositeUnit F G RF RG αF αG)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let RFG := rightDerivedOfGrothendieck (F ⋙ G)
  let βFG := rightDerivedOfGrothendieckUnit (F ⋙ G)
  let : RFG.IsRightDerivedFunctor βFG
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    rightDerivedOfGrothendieck_isRightDerived (F ⋙ G)
  let τ := RFG.rightDerivedDesc βFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (RF ⋙ RG) (derivedCompositeUnit F G RF RG αF αG)
  have hτ : IsIso τ := by
    apply isIso_natTrans_of_isIso_app_on_kInjectives τ
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A)
    intro I hI
    let : IsIso ((derivedCompositeUnit F G RF RG αF αG).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := hβ I hI
    let : IsIso ((βFG).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective
        ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
        RFG βFG I hI
    have hfac := Functor.rightDerived_fac_app RFG βFG
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (RF ⋙ RG)
      (derivedCompositeUnit F G RF RG αF αG)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)
    let x := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I
    let i := (βFG).app x
    let g := τ.app (DerivedCategory.Qh.obj x)
    have hi : IsIso i := by
      dsimp [i]
      infer_instance
    have hcomp : IsIso (i ≫ g) := by
      dsimp [i, g]
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left i g
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    RFG βFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (RF ⋙ RG) (derivedCompositeUnit F G RF RG αF αG)).2 hτ

variable {C : Type u} [Category.{v} C]

private abbrev overMapLiftIndex (X Y : C) (f : X ⟶ Y) (V : Over Y) :=
  {g : V.left ⟶ X // g ≫ f = V.hom}

private abbrev overMapCostructured (X Y : C) (f : X ⟶ Y) (V : Over Y) :=
  CostructuredArrow (Over.map f).op (op V)

private noncomputable def overMapLiftObject {X Y : C} (f : X ⟶ Y) (V : Over Y)
    (g : overMapLiftIndex X Y f V) : overMapCostructured X Y f V :=
  CostructuredArrow.mk (Y := op (Over.mk g.1)) <|
    (Over.homMk (U := V) (V := (Over.map f).obj (Over.mk g.1)) (𝟙 V.left)
      (by simpa [Over.map_obj_hom] using g.2)).op

private noncomputable def overMapLiftInclusion {X Y : C} (f : X ⟶ Y) (V : Over Y) :
    Discrete (overMapLiftIndex X Y f V) ⥤ overMapCostructured X Y f V where
  obj g := overMapLiftObject f V g.as
  map := by
    intro g g' h
    have hg : g.as.1 = g'.as.1 := congrArg Subtype.val (Discrete.eq_of_hom h)
    let α : Over.mk g'.as.1 ⟶ Over.mk g.as.1 := Over.homMk (𝟙 V.left) (by
      simpa using hg)
    let β : overMapLiftObject f V g.as ⟶ overMapLiftObject f V g'.as :=
      CostructuredArrow.homMk α.op (by
        apply Opposite.unop_injective
        apply Over.OverMorphism.ext
        change (𝟙 V.left) ≫ 𝟙 V.left = 𝟙 V.left
        simp)
    exact β
  map_id := by
    intro g
    apply CostructuredArrow.hom_ext
    apply Opposite.unop_injective
    apply Over.OverMorphism.ext
    change 𝟙 V.left = 𝟙 V.left
    rfl
  map_comp := by
    intro g g' g'' h₁ h₂
    apply CostructuredArrow.hom_ext
    apply Opposite.unop_injective
    apply Over.OverMorphism.ext
    change (𝟙 V.left) = (𝟙 V.left) ≫ (𝟙 V.left)
    simp

/-- A morphism of `overMapCostructured X Y f V` is compatible with the structure maps on the
underlying morphisms of `C`. -/
private lemma overMapCostructured_hom_left_comp {X Y : C} {f : X ⟶ Y} {V : Over Y}
    {c c' : overMapCostructured X Y f V} (h : c ⟶ c') :
    c'.hom.unop.left ≫ h.left.unop.left = c.hom.unop.left := by
  have hwop : c'.hom.unop ≫ (Over.map f).map (h.left.unop) = c.hom.unop := by
    simpa using congrArg (fun e => e.unop) (CostructuredArrow.w h)
  simpa using congrArg Over.Hom.left hwop

private noncomputable def overMapLiftProjection {X Y : C} (f : X ⟶ Y) (V : Over Y) :
    overMapCostructured X Y f V ⥤ Discrete (overMapLiftIndex X Y f V) where
  obj c := Discrete.mk ⟨c.hom.unop.left ≫ c.left.unop.hom, by
    simpa [Over.map_obj_hom] using (Over.w c.hom.unop)⟩
  map := by
    intro c c' h
    apply Discrete.eqToHom
    apply Subtype.ext
    have hw' := Over.w (h.left.unop)
    have hhom' := overMapCostructured_hom_left_comp h
    change c.hom.unop.left ≫ c.left.unop.hom =
      c'.hom.unop.left ≫ c'.left.unop.hom
    calc
      c.hom.unop.left ≫ c.left.unop.hom =
          (c'.hom.unop.left ≫ h.left.unop.left) ≫ c.left.unop.hom := by rw [← hhom']
      _ = c'.hom.unop.left ≫ (h.left.unop.left ≫ c.left.unop.hom) := by
        rw [Category.assoc]
      _ = c'.hom.unop.left ≫ c'.left.unop.hom := by rw [hw']

private lemma overMapLiftInclusion_map_left {X Y : C} (f : X ⟶ Y) (V : Over Y)
    (g g' : Discrete (overMapLiftIndex X Y f V)) (h : g ⟶ g') :
    ((overMapLiftInclusion f V).map h).left =
      (Over.homMk (U := Over.mk g'.as.1) (V := Over.mk g.as.1) (𝟙 V.left)
        (by simpa using congrArg Subtype.val (Discrete.eq_of_hom h))).op :=
  rfl

private lemma overMapLiftInclusion_obj_hom_left {X Y : C} (f : X ⟶ Y) (V : Over Y)
    (g : Discrete (overMapLiftIndex X Y f V)) :
    ((overMapLiftInclusion f V).obj g).hom.unop.left = 𝟙 V.left :=
  rfl

private lemma overMapLiftInclusion_obj_left {X Y : C} (f : X ⟶ Y) (V : Over Y)
    (g : Discrete (overMapLiftIndex X Y f V)) :
    ((overMapLiftInclusion f V).obj g).left = op (Over.mk g.as.1) :=
  rfl

private noncomputable def overMapLiftUnitApp {X Y : C} (f : X ⟶ Y) (V : Over Y)
    (c : overMapCostructured X Y f V) : c ⟶
      (overMapLiftInclusion f V).obj ((overMapLiftProjection f V).obj c) := by
  let g : overMapLiftIndex X Y f V :=
    ⟨c.hom.unop.left ≫ c.left.unop.hom, by
      simpa [Over.map_obj_hom] using (Over.w c.hom.unop)⟩
  let α : Over.mk g.1 ⟶ c.left.unop := Over.homMk c.hom.unop.left (by
    dsimp [g])
  let β : c ⟶ (overMapLiftInclusion f V).obj ((overMapLiftProjection f V).obj c) :=
    CostructuredArrow.homMk α.op (by
      apply Opposite.unop_injective
      apply Over.OverMorphism.ext
      change 𝟙 V.left ≫ c.hom.unop.left = c.hom.unop.left
      exact Category.id_comp _)
  exact β

private noncomputable def overMapLiftAdjunction {X Y : C} (f : X ⟶ Y) (V : Over Y) :
    overMapLiftProjection f V ⊣ overMapLiftInclusion f V := by
  refine Adjunction.mkOfUnitCounit
    { unit :=
        { app := overMapLiftUnitApp f V
          naturality := by
            intro c c' h
            have hhom' := overMapCostructured_hom_left_comp h
            simp only [Functor.id_map]
            apply CostructuredArrow.hom_ext
            apply Opposite.unop_injective
            apply Over.OverMorphism.ext
            rw [Functor.comp_map]
            change c'.hom.unop.left ≫ h.left.unop.left =
              𝟙 V.left ≫ c.hom.unop.left
            rw [hhom']
            simp }
      counit :=
        { app := fun g => Discrete.eqToHom (by
            apply Subtype.ext
            simp [overMapLiftProjection, overMapLiftInclusion, overMapLiftObject])
          naturality := by
            intro g g' h
            subsingleton }
      left_triangle := by
        ext c
        subsingleton
      right_triangle := by
        ext g
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
          Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
          Category.id_comp, CostructuredArrow.comp_left, NatTrans.id_app',
          CostructuredArrow.id_left]
        change (𝟙 V.left ≫ 𝟙 V.left) = 𝟙 V.left
        simp }

private lemma overMapCostructured_hasExactColimits [UnivLE.{max u v, w}]
    {X Y : C} (f : X ⟶ Y) (V : Over Y) :
    HasExactColimitsOfShape (overMapCostructured X Y f V) Ab.{w} := by
  -- The index type of the final discrete subcategory is a subtype of `V.left ⟶ X`, hence lives
  -- in `Type v`; AB4 has to be applied to `Ab.{w}` at that size, so it is transported into
  -- `Type w` along two equivalences of discrete categories, both final, so exactness pulls back
  -- along them.  This is `costructuredArrow_hasExactColimitsOfShape` of
  -- `StacksFrontier/Homology/Injectives/Sheaf/InternalHomExact.lean`, for `Over.map f` in place of
  -- `Over.forget`.
  have : Small.{w} (ULift.{u} (overMapLiftIndex X Y f V)) := inferInstance
  let e₀ : Discrete (Shrink.{w} (ULift.{u} (overMapLiftIndex X Y f V))) ⥤
      Discrete (ULift.{u} (overMapLiftIndex X Y f V)) :=
    (Discrete.equivalence (equivShrink.{w} (ULift.{u} (overMapLiftIndex X Y f V)))).inverse
  let e₁ : Discrete (ULift.{u} (overMapLiftIndex X Y f V)) ⥤
      Discrete (overMapLiftIndex X Y f V) :=
    (Discrete.equivalence (Equiv.ulift.{u})).functor
  have h₀ : e₀.Final := inferInstanceAs
    ((Discrete.equivalence
      (equivShrink.{w} (ULift.{u} (overMapLiftIndex X Y f V)))).inverse).Final
  have h₁ : e₁.Final := inferInstanceAs
    ((Discrete.equivalence (Equiv.ulift.{u})).functor).Final
  have : HasExactColimitsOfShape
      (Discrete (Shrink.{w} (ULift.{u} (overMapLiftIndex X Y f V)))) Ab.{w} :=
    AB4OfSize.ofShape (C := Ab.{w}) (Shrink.{w} (ULift.{u} (overMapLiftIndex X Y f V)))
  let : (overMapLiftInclusion f V).Final :=
    Functor.final_of_adjunction (overMapLiftAdjunction f V)
  have : (e₀ ⋙ e₁ ⋙ overMapLiftInclusion f V).Final :=
    Functor.final_comp e₀ (e₁ ⋙ overMapLiftInclusion f V)
  exact hasExactColimitsOfShape_of_final Ab.{w} (e₀ ⋙ e₁ ⋙ overMapLiftInclusion f V)

open CategoryTheory.Limits in
private noncomputable def overMapLanEvaluationIsoColim [UnivLE.{max u v, w}]
    {X Y : C} (f : X ⟶ Y) (V : Over Y)
    [∀ H : (Over X)ᵒᵖ ⥤ Ab.{w}, (Over.map f).op.HasLeftKanExtension H]
    (hcolim : Limits.HasColimitsOfShape (overMapCostructured X Y f V) Ab.{w}) :
    (Over.map f).op.lan ⋙ (evaluation (Over Y)ᵒᵖ Ab.{w}).obj (op V) ≅
      (Functor.whiskeringLeft _ _ Ab.{w}).obj
        (CostructuredArrow.proj (Over.map f).op (op V)) ⋙
          (colim (J := overMapCostructured X Y f V) (C := Ab.{w})) := by
  let := hcolim
  exact NatIso.ofComponents (fun H => IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit (Over.map f).op H (op V))
      (colimit.isColimit _)) (fun {H₁ H₂} φ => by
        apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
          (Over.map f).op H₁ (op V)).hom_ext
        intro T
        have h₁ := fun (H : (Over X)ᵒᵖ ⥤ Ab.{w}) =>
          IsColimit.comp_coconePointUniqueUpToIso_hom
            (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
              (Over.map f).op H (op V))
            (colimit.isColimit _) T
        have h₂ := congr_app ((Over.map f).op.lanUnit.naturality φ) T.left
        dsimp at h₁ h₂ ⊢
        simp only [Category.assoc] at h₁ ⊢
        simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
        simp only [Category.assoc] at h₂ ⊢
        rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
          ι_colimMap, Functor.whiskerLeft_app]
        rfl)

open CategoryTheory.Limits in
private theorem overMap_op_lan_preservesFiniteLimits [UnivLE.{max u v, w}]
    {X Y : C} (f : X ⟶ Y) :
    Limits.PreservesFiniteLimits
      ((Over.map f).op.lan : ((Over X)ᵒᵖ ⥤ Ab.{w}) ⥤
        (Over Y)ᵒᵖ ⥤ Ab.{w}) := by
  apply Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro I _ _
  apply Limits.preservesLimitsOfShape_of_evaluation _ I
  intro V
  let : ∀ H : (Over X)ᵒᵖ ⥤ Ab.{w},
      (Over.map f).op.HasLeftKanExtension H := fun H =>
    (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
      (Over.map f).op H).hasLeftKanExtension
  let : HasExactColimitsOfShape (overMapCostructured X Y f V.unop) Ab.{w} :=
    overMapCostructured_hasExactColimits f V.unop
  let hcolim : Limits.HasColimitsOfShape
      (overMapCostructured X Y f V.unop) Ab.{w} := inferInstance
  exact Limits.preservesLimitsOfShape_of_natIso
    (overMapLanEvaluationIsoColim f V.unop hcolim).symm

open CategoryTheory.Limits in
/-- **The `Ab`-valued left Kan extension along `(Over.map f).op` preserves finite limits.** The
value of the Kan extension at `V : Over Y` is a colimit over
`CostructuredArrow (Over.map f).op (op V)`, and that index category admits a *final* discrete
subcategory, namely the liftings `{g : V.left ⟶ X // g ≫ f = V.hom}` of `V` through `f`;
colimits of discrete shape in `Ab` are exact by Grothendieck's axiom AB4, and finality transports
that exactness.

Composed with sheafification this is the left exactness of extension by zero along `Over.map f`,
which is what makes the restriction of abelian sheaves along a morphism of localized sites
preserve injective objects.

The coefficient universe `w` need only dominate that of the site, `UnivLE.{max u v, w}`: that is
where the index type, which lives in `Type v`, is transported into `Type w` so that AB4 may be
applied to `Ab.{w}` at its size. In particular a site whose objects form a `Type (u + 1)` with
morphisms in `Type u` and whose coefficients are `Ab.{max (u + 1) v}` is covered, since
`UnivLE.{u + 1, max (u + 1) v}` holds unconditionally. This is the analogue for `Over.map f` of
`Stacks.Injectives.lan_overForget_preservesFiniteLimits`. -/
@[sga "4 IV 11.3.1" "partial"]
alias preservesFiniteLimits_overMap_op_lan := overMap_op_lan_preservesFiniteLimits

/-- Sheaves of abelian groups on the localization of a site at an object. -/
abbrev AbelianSheaves (J : GrothendieckTopology C) (U : C) :=
  Sheaf (J.over U) Ab.{max u v}

/-- Inverse image between localized sites, induced by a morphism of the underlying site. -/
noncomputable abbrev overPullback (J : GrothendieckTopology C) {U V : C} (f : U ⟶ V) :
    AbelianSheaves J V ⥤ AbelianSheaves J U :=
  J.overMapPullback Ab.{max u v} f

/-- The left adjoint of the inverse image between localized sites is left exact. It is the
sheafified left Kan extension along `(Over.map f).op`, whose left exactness is the finality
argument of this file. -/
lemma overMapSheafPullback_preservesFiniteLimits
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [∀ U : C, HasSheafify (J.over U) Ab.{max u v}] :
    Limits.PreservesFiniteLimits
      ((Over.map f).sheafPullback Ab.{max u v} (J.over X) (J.over Y)) := by
  let G := Over.map f
  let adj := G.sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y)
  let adjLan := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{max u v}
    (J.over X) (J.over Y)
  let e := Adjunction.leftAdjointUniq adj adjLan
  let : Limits.PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback G Ab.{max u v}
        (J.over X) (J.over Y)) := by
    dsimp [Functor.sheafPullbackConstruction.sheafPullback]
    let : Limits.PreservesFiniteLimits
        ((Over.map f).op.lan : ((Over X)ᵒᵖ ⥤ Ab.{max u v}) ⥤
          (Over Y)ᵒᵖ ⥤ Ab.{max u v}) := overMap_op_lan_preservesFiniteLimits f
    exact Limits.comp_preservesFiniteLimits _ _
  exact Limits.preservesFiniteLimits_of_natIso e.symm

/-- The restriction functor `overPullback J f` along `f : X ⟶ Y` sends a K-injective complex of
abelian sheaves on `C/Y` to a K-injective complex of abelian sheaves on `C/X`. -/
lemma overPullback_map_isKInjective
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [∀ U : C, HasSheafify (J.over U) Ab.{max u v}]
    (I : CochainComplex (AbelianSheaves J Y) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((overPullback J f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let G := Over.map f
  let adj := G.sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y)
  let : Limits.PreservesFiniteLimits (G.sheafPullback Ab.{max u v}
    (J.over X) (J.over Y)) := overMapSheafPullback_preservesFiniteLimits J f
  let : Limits.PreservesFiniteColimits (G.sheafPullback Ab.{max u v}
      (J.over X) (J.over Y)) :=
    (adj.leftAdjoint_preservesColimits.{max u v, max u v}).preservesFiniteColimits
  let : ((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
      (J.over X) (J.over Y)).IsRightAdjoint :=
    (G.sheafAdjunctionCocontinuous Ab.{max u v}
      (J.over X) (J.over Y)).isRightAdjoint
  let : ((Over.map f).sheafPushforwardCocontinuous Ab.{max u v}
      (J.over X) (J.over Y)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (overPullback J f).Additive :=
    ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v}
      (J.over X) (J.over Y)).left_adjoint_additive
  let : (G.sheafPullback Ab.{max u v} (J.over X) (J.over Y)).Additive :=
    adj.left_adjoint_additive
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (overPullback J f)
    (G.sheafPullback Ab.{max u v} (J.over X) (J.over Y)) adj I

/-- Direct image between localized sites, induced by a morphism of the underlying site. -/
noncomputable abbrev overPushforward (J : GrothendieckTopology C) {U V : C} (f : U ⟶ V) :
    AbelianSheaves J U ⥤ AbelianSheaves J V :=
  (Over.map f).sheafPushforwardCocontinuous Ab.{max u v} (J.over U) (J.over V)

/-- Direct image on abelian sheaves over localized sites is additive. -/
noncomputable instance overPushforward_additive (J : GrothendieckTopology C)
    {U V : C} (f : U ⟶ V) : (overPushforward J f).Additive := by
  let _ := ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v}
    (J.over U) (J.over V)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- Inverse image on abelian sheaves over localized sites is additive. -/
noncomputable instance overPullback_additive (J : GrothendieckTopology C)
    {U V : C} (f : U ⟶ V) : (overPullback J f).Additive := by
  let _ := overPushforward_additive J f
  exact ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v}
    (J.over U) (J.over V)).left_adjoint_additive

/-- **Stacks 0EZ0.** For a Cartesian square
```
  X' --a--> X
  |b         |c
  Y' --d--> Y
```
in a site, inverse image along `d` after derived direct image along `c` is naturally isomorphic
to derived direct image along `b` after inverse image along `a`.

All four derived functors are arbitrary choices with their canonical transformations from the
corresponding functors on homotopy categories. -/
@[stacks 0EZ0]
noncomputable def derivedOverPushforwardBaseChangeIso
    (J : GrothendieckTopology C) {X' X Y' Y : C}
    (a : X' ⟶ X) (b : X' ⟶ Y') (c : X ⟶ Y) (d : Y' ⟶ Y)
    (h : IsPullback a b c d)
    [∀ U : C, HasSheafify (J.over U) Ab.{max u v}]
    [HasDerivedCategory.{wX} (AbelianSheaves J X)]
    [HasDerivedCategory.{wY} (AbelianSheaves J Y)]
    [HasDerivedCategory.{wU} (AbelianSheaves J X')]
    [HasDerivedCategory.{wV'} (AbelianSheaves J Y')]
    (Rc : DerivedCategory (AbelianSheaves J X) ⥤
      DerivedCategory (AbelianSheaves J Y))
    (Rb : DerivedCategory (AbelianSheaves J X') ⥤
      DerivedCategory (AbelianSheaves J Y'))
    (Ra : DerivedCategory (AbelianSheaves J X) ⥤
      DerivedCategory (AbelianSheaves J X'))
    (Rd : DerivedCategory (AbelianSheaves J Y) ⥤
      DerivedCategory (AbelianSheaves J Y'))
    (αc : homotopyToDerived (overPushforward J c) ⟶ DerivedCategory.Qh ⋙ Rc)
    (αb : homotopyToDerived (overPushforward J b) ⟶ DerivedCategory.Qh ⋙ Rb)
    (αa : homotopyToDerived (overPullback J a) ⟶ DerivedCategory.Qh ⋙ Ra)
    (αd : homotopyToDerived (overPullback J d) ⟶ DerivedCategory.Qh ⋙ Rd)
    [Rc.IsRightDerivedFunctor αc
      (HomotopyCategory.quasiIso (AbelianSheaves J X) (ComplexShape.up ℤ))]
    [Rb.IsRightDerivedFunctor αb
      (HomotopyCategory.quasiIso (AbelianSheaves J X') (ComplexShape.up ℤ))]
    [Ra.IsRightDerivedFunctor αa
      (HomotopyCategory.quasiIso (AbelianSheaves J X) (ComplexShape.up ℤ))]
    [Rd.IsRightDerivedFunctor αd
      (HomotopyCategory.quasiIso (AbelianSheaves J Y) (ComplexShape.up ℤ))] :
    Rc ⋙ Rd ≅ Ra ⋙ Rb := by
  let Fc := overPushforward J c
  let Gd := overPullback J d
  let Ga := overPullback J a
  let Fb := overPushforward J b
  let : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves J X) := sheaf_isGrothendieckAbelian (J.over X)
  let αleft := derivedCompositeUnit Fc Gd Rc Rd αc αd
  have hαleft : (Rc ⋙ Rd).IsRightDerivedFunctor αleft
      (HomotopyCategory.quasiIso (AbelianSheaves J X) (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived Fc Gd Rc Rd αc αd
    intro I hI
    let : IsIso (αc.app
        ((HomotopyCategory.quotient (AbelianSheaves J X) (ComplexShape.up ℤ)).obj I)) :=
      rightDerivedUnit_isIso_app_of_isKInjective
        (Fc.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
        Rc αc I hI
    let : IsIso αd := exactRightDerivedUnit_isIso Gd Rd αd
    dsimp [derivedCompositeUnit]
    infer_instance
  let αright := derivedCompositeUnit Ga Fb Ra Rb αa αb
  have hαright : (Ra ⋙ Rb).IsRightDerivedFunctor αright
      (HomotopyCategory.quasiIso (AbelianSheaves J X) (ComplexShape.up ℤ)) := by
    apply derivedComposite_isRightDerived Ga Fb Ra Rb αa αb
    intro I hI
    let : IsIso αa := exactRightDerivedUnit_isIso Ga Ra αa
    let I' := ((Ga.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    let : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
        (AbelianSheaves J X') := sheaf_isGrothendieckAbelian (J.over X')
    let : CochainComplex.IsKInjective I' := overPullback_map_isKInjective J a I
    have hαb' := rightDerivedUnit_isIso_app_of_isKInjective
      (Fb.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      Rb αb I' (by infer_instance)
    dsimp [derivedCompositeUnit]
    have hαb : IsIso (αb.app
        ((Ga.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (AbelianSheaves J X)
            (ComplexShape.up ℤ)).obj I))) := by
      change IsIso (αb.app ((HomotopyCategory.quotient (AbelianSheaves J X')
        (ComplexShape.up ℤ)).obj I'))
      exact hαb'
    let := hαb
    infer_instance
  let : IsGrothendieckAbelian.{max u v, max u v, max u v + 1}
      (AbelianSheaves J X') := sheaf_isGrothendieckAbelian (J.over X')
  let : IsIso (J.overMapPushforwardBaseChange Ab.{max u v} h.toCommSq) :=
    J.isIso_overMapPushforwardBaseChange Ab.{max u v} h
  let under : Fc ⋙ Gd ≅ Ga ⋙ Fb :=
    asIso (J.overMapPushforwardBaseChange Ab.{max u v} h.toCommSq)
  let underH :=
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (Fc ⋙ Gd))
      (ComplexShape.up ℤ)).symm ≪≫
      Functor.mapHomotopyCategoryCompIso under (ComplexShape.up ℤ)
  let underQ := Functor.isoWhiskerRight underH DerivedCategory.Qh
  exact Functor.rightDerivedNatIso (Rc ⋙ Rd) (Ra ⋙ Rb) αleft αright
    (HomotopyCategory.quasiIso (AbelianSheaves J X) (ComplexShape.up ℤ)) underQ

end Stacks.Cohomology.Localization

end
