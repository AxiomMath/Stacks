module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexOfAFamily

/-!
# The augmentation of the Čech complex of a family, with sheaves of modules as coefficients

Let `C` be a site with binary products, let `R` be a sheaf of rings on `C`, let `F` be a sheaf
of `R`-modules and let `{U_i → X}` be a family of morphisms with fixed target.
`Stacks.CechSite.SheafLevel.complexFunctor` assembles the sheaves
`j_{U_{i_0} ×_X ⋯ ×_X U_{i_p}, *} j^{-1} F` into a cochain complex of sheaves of `R`-modules.
This file supplies its **augmentation**: a morphism of sheaves of modules

`F ⟶ ∏_{i} j_{U_i, *} j^{-1} F`

onto the degree-zero term, killed by the first differential, hence a morphism

`F[0] ⟶ Č(E, F)`

out of the complex concentrated in degree `0`, natural in `F`.

## Main definitions

* `Stacks.CechSite.SheafLevel.augmentationAt`: for one object `V`, the unit
  `F ⟶ j_{V,*} j_V^{-1} F` of the adjunction between restriction to `C/V` and direct image.
* `Stacks.CechSite.SheafLevel.augmentation`: the augmentation `F ⟶ Č⁰(E, F)`.
* `Stacks.CechSite.SheafLevel.augmentationHom`: the augmentation as a morphism of cochain
  complexes out of `F[0]`.
* `Stacks.CechSite.SheafLevel.augmentationNatTrans`: that morphism, natural in `F`.

## Main results

* `Stacks.CechSite.SheafLevel.augmentationAt_apply`: on sections over `Y`, the unit is `F`
  applied to the second projection `V ⨯ Y ⟶ Y`.
* `Stacks.CechSite.SheafLevel.augmentationAt_comp_restriction`: the units are compatible with
  the transition maps of `Stacks.CechSite.SheafLevel.restriction`, which is what makes them a
  cone over the Čech diagram.
* `Stacks.CechSite.SheafLevel.augmentation_comp_d`: `augmentation ≫ d⁰ = 0`.

## Implementation notes

The sections formula for the unit is the one piece that is not formal.  The unit of
`SheafOfModules.overPushforwardOverAdj V` is a composite of `pushforwardNatTrans`,
`pushforwardCongr` and `pushforwardComp`, but Mathlib's
`SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app` evaluates that composite on
sections by `rfl`, as restriction along the counit of `CategoryTheory.Over.forgetAdjStar V`;
and `CategoryTheory.Over.forgetAdjStar_counit_app` identifies that counit with
`Limits.prod.snd`.  The second step is *not* definitional — `Limits.prod.snd` reaches the
binary product through `getLimitCone`, which is not exposed — so
`augmentationAt_apply'` records the counit form, which is `rfl`, and `augmentationAt_apply`
transports it along that identification with an explicit `congrArg`.

The same opacity is why the proofs below are written as explicit terms rather than with
`rw`/`simp`: once a goal mentions both `Limits.prod.snd` and `Limits.prod.functor`, or both
`((complexFunctor R E).obj F).X 0` and the cosimplicial object it unfolds to, the goal is
reported as not type-correct at `implicit` transparency and no rewrite matches, while the
corresponding term elaborates.  This is the same obstruction documented at
`Stacks.CechSite.SheafLevel.starMap_comp_snd`.

That `augmentation ≫ d⁰ = 0` comes down to `augmentation_comp_delta_eq`: the two coface maps
`δ 0, δ 1 : Č⁰ ⟶ Č¹` agree after the augmentation, because composing the unit at
`U_{i_0} ×_X ⋯` with a transition map gives the unit at the smaller object, independently of
which index was dropped.  The alternating sum of two equal terms with opposite signs is zero.

`augmentationHom` and `augmentationNatTrans` ask for `Limits.HasZeroObject` on the sheaves of
modules, which `CategoryTheory.HomologicalComplex.single` needs and which the variables of
`Stacks.CechSite.SheafLevel.complexFunctor` do not supply: those assume sheafification and
local bijectivity only on the slices `J.over V`, whereas `SheafOfModules.instAbelian` — the
source of a zero object — asks for them on `J` itself.  It is left as an instance argument
rather than strengthened into the file's variables, so that the complex and its augmentation
keep the generality they had.

**The quasi-isomorphism is not here.**  Nothing below asserts that `augmentationHom` is a
quasi-isomorphism, i.e. that `Č(E, F)` is a resolution of `F`.  For a family covering a
*terminal* object that statement is
`Stacks.CechSite.SheafLevel.quasiIso_augmentationHom_of_coversTop` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelComplexDegreeZero.lean`; terminality
of the target cannot be dropped, by the counterexample recorded in the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelComplexSections.lean`.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v' u' v u

namespace Stacks.CechSite.SheafLevel

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The augmentation at one object `V`**: the unit `F ⟶ j_{V,*} j_V^{-1} F` of the
adjunction between restriction to the localized site `C/V` and direct image along the
localization morphism, with its codomain spelled as
`Stacks.CechSite.SheafLevel.directImage`. -/
noncomputable abbrev augmentationAt (F : SheafOfModules.{u} R) (V : C) :
    F ⟶ (directImage R V).obj F :=
  (SheafOfModules.overPushforwardOverAdj V).unit.app F

/-- The sections of `Stacks.CechSite.SheafLevel.augmentationAt` are the restriction maps of
`F` along the counit of `CategoryTheory.Over.forgetAdjStar`, on the nose.  This is the
spelling in which the formula is definitional; see
`Stacks.CechSite.SheafLevel.augmentationAt_apply` for the useful one. -/
theorem augmentationAt_apply' (F : SheafOfModules.{u} R) (V : C) (Y : Cᵒᵖ)
    (x : ToType (F.val.obj Y)) :
    (ConcreteCategory.hom ((augmentationAt R F V).val.app Y)) x =
      (ConcreteCategory.hom
        (F.val.presheaf.map ((Over.forgetAdjStar V).counit.app Y.unop).op)) x := rfl

/-- **The sections of the augmentation at `V`**: over `Y` it is `F` applied to the second
projection `V ⨯ Y ⟶ Y`, the map `F(Y) ⟶ F(V ⨯ Y)`. -/
theorem augmentationAt_apply (F : SheafOfModules.{u} R) (V : C) (Y : Cᵒᵖ)
    (x : ToType (F.val.obj Y)) :
    (ConcreteCategory.hom ((augmentationAt R F V).val.app Y)) x =
      (ConcreteCategory.hom
        (F.val.presheaf.map (prod.snd : V ⨯ Y.unop ⟶ Y.unop).op)) x :=
  (augmentationAt_apply' R F V Y x).trans
    (congrArg (fun g : V ⨯ Y.unop ⟶ Y.unop =>
      (ConcreteCategory.hom (F.val.presheaf.map g.op)) x)
      (Over.forgetAdjStar_counit_app V Y.unop))

/-- **The augmentations form a cone over the Čech diagram.**  Composing the unit at `V` with
the transition map of `f : W ⟶ V` gives the unit at `W`: both are `F` applied to a second
projection, and `prod.map f (𝟙 Y) ≫ prod.snd = prod.snd`. -/
theorem augmentationAt_comp_restriction (F : SheafOfModules.{u} R) {V W : C} (f : W ⟶ V) :
    augmentationAt R F V ≫ restriction R F f = augmentationAt R F W := by
  ext Y x
  have h1 : (ConcreteCategory.hom ((augmentationAt R F V ≫ restriction R F f).val.app Y)) x =
      (ConcreteCategory.hom ((restriction R F f).val.app Y))
        ((ConcreteCategory.hom ((augmentationAt R F V).val.app Y)) x) := rfl
  have key : F.val.presheaf.map (prod.snd : V ⨯ Y.unop ⟶ Y.unop).op ≫
      F.val.presheaf.map (((prod.functor (C := C)).map f).app Y.unop).op =
      F.val.presheaf.map (prod.snd : W ⨯ Y.unop ⟶ Y.unop).op :=
    (F.val.presheaf.map_comp _ _).symm.trans
      (congrArg F.val.presheaf.map
        (op_comp.symm.trans (congrArg Quiver.Hom.op (starMap_comp_snd f Y.unop))))
  rw [h1, restriction_apply, augmentationAt_apply, augmentationAt_apply]
  exact ConcreteCategory.congr_hom key x

omit [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The augmentations are natural in the sheaf of modules, being the components of an
adjunction unit. -/
theorem augmentationAt_naturality {F G : SheafOfModules.{u} R} (φ : F ⟶ G) (V : C) :
    augmentationAt R F V ≫ (directImage R V).map φ = φ ≫ augmentationAt R G V :=
  ((SheafOfModules.overPushforwardOverAdj V).unit.naturality φ).symm

section Complex

variable {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} (SheafOfModules.{u} R)]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

/-- The cosimplicial object of sheaves of `R`-modules whose alternating coface map complex is
`Stacks.CechSite.SheafLevel.complexFunctor`: in degree `n` the product, over the
`(n+1)`-tuples of members of the family, of `j_{U_{i_0} ×_X ⋯ ×_X U_{i_n}, *} j^{-1} F`. -/
noncomputable abbrev cosimplicialObj (F : SheafOfModules.{u} R) :
    CosimplicialObject (SheafOfModules.{u} R) :=
  (FormalCoproduct.cosimplicialObjectFunctor (cechSimplicialObject E)).obj
    ((Over.forget X).op ⋙ diagramObj R F)

omit [HasProducts.{w} (SheafOfModules.{u} R)] in
/-- The presheaf fed to the Čech construction acts on a morphism of the slice by the
transition map of its underlying morphism of `C`. -/
theorem evalPresheaf_map (F : SheafOfModules.{u} R) {V W : Over X} (ψ : W ⟶ V) :
    ((Over.forget X).op ⋙ diagramObj R F).map ψ.op = restriction R F ψ.left := rfl

/-- **The augmentation of the sheaf-level Čech complex**: the morphism of sheaves of
`R`-modules `F ⟶ Č⁰(E, F)` whose component at the index `i` is the unit
`F ⟶ j_{U_i, *} j^{-1} F`. -/
noncomputable def augmentation (F : SheafOfModules.{u} R) :
    F ⟶ ((complexFunctor R E).obj F).X 0 :=
  Pi.lift fun _ ↦ augmentationAt R F _

/-- The components of the augmentation are the units. -/
theorem augmentation_comp_pi (F : SheafOfModules.{u} R)
    (i : ((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).I) :
    augmentation R E F ≫ Pi.π _ i =
      augmentationAt R F
        (((cechSimplicialObject E).obj (op (⦋0⦌ : SimplexCategory))).obj i).left :=
  Pi.lift_π _ _

/-- If `h ≫ p = k ≫ t` and `a ≫ k = b`, then `(a ≫ h) ≫ p = b ≫ t`. -/
private theorem comp_comp_eq_of_comp_eq {𝒟 : Type*} [Category 𝒟] {A P Q M Z : 𝒟}
    (a : A ⟶ P) (h : P ⟶ Q) (p : Q ⟶ Z) (k : P ⟶ M) (t : M ⟶ Z) (b : A ⟶ M)
    (e : h ≫ p = k ≫ t) (hb : a ≫ k = b) : (a ≫ h) ≫ p = b ≫ t := by
  rw [Category.assoc, e, ← Category.assoc, hb]

/-- The components of a coface map of the Čech cosimplicial object are the transition maps
of the morphisms of fibre products that forget one index. -/
theorem delta_comp_pi (F : SheafOfModules.{u} R) (i : Fin 2)
    (j : ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).I) :
    (cosimplicialObj R E F).δ i ≫ Pi.π _ j =
      Pi.π _ (((cechSimplicialObject E).map (SimplexCategory.δ i).op).f j) ≫
        restriction R F
          (((cechSimplicialObject E).map (SimplexCategory.δ i).op).φ j).left :=
  Pi.lift_π _ _

/-- Each component of the augmentation followed by a coface map is the unit at the fibre
product indexed by the full pair — in particular it does not depend on which of the two
indices the coface map dropped. -/
theorem augmentation_comp_delta_comp_pi (F : SheafOfModules.{u} R) (i : Fin 2)
    (j : ((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).I) :
    (augmentation R E F ≫ (cosimplicialObj R E F).δ i) ≫ Pi.π _ j =
      augmentationAt R F
        (((cechSimplicialObject E).obj (op (⦋1⦌ : SimplexCategory))).obj j).left :=
  (comp_comp_eq_of_comp_eq _ _ _ _ _ _ (delta_comp_pi R E F i j)
    (augmentation_comp_pi R E F _)).trans (augmentationAt_comp_restriction R F _)

/-- **The two coface maps agree after the augmentation.** -/
theorem augmentation_comp_delta_eq (F : SheafOfModules.{u} R) (i i' : Fin 2) :
    augmentation R E F ≫ (cosimplicialObj R E F).δ i =
      augmentation R E F ≫ (cosimplicialObj R E F).δ i' :=
  Pi.hom_ext _ _ fun j ↦
    (augmentation_comp_delta_comp_pi R E F i j).trans
      (augmentation_comp_delta_comp_pi R E F i' j).symm

/-- **The augmentation lands in the degree-zero cocycles**: `augmentation ≫ d⁰ = 0`.  The
first Čech differential is the difference of the two coface maps, and those agree after the
augmentation. -/
theorem augmentation_comp_d (F : SheafOfModules.{u} R) :
    augmentation R E F ≫ ((complexFunctor R E).obj F).d 0 1 = 0 := by
  have hsum : ∀ g : F ⟶ (cosimplicialObj R E F).obj (⦋0⦌ : SimplexCategory),
      g ≫ (cosimplicialObj R E F).δ 0 = g ≫ (cosimplicialObj R E F).δ 1 →
      g ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cosimplicialObj R E F).δ i) = 0 := by
    intro g hg
    rw [Fin.sum_univ_two, Preadditive.comp_add, Preadditive.comp_zsmul,
      Preadditive.comp_zsmul, hg]
    simp
  have hd : ((complexFunctor R E).obj F).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cosimplicialObj R E F).δ i :=
    Stacks.CategoryTheory.CechComplex.alternatingCofaceMapComplex_obj_d
      (cosimplicialObj R E F) 0
  rw [hd]
  exact hsum _ (augmentation_comp_delta_eq R E F 0 1)

/-- The functoriality of the Čech complex in the sheaf of modules is componentwise the
functoriality of `Stacks.CechSite.SheafLevel.directImage`. -/
theorem map_f_comp_pi {F G : SheafOfModules.{u} R} (φ : F ⟶ G) (n : ℕ)
    (j : ((cechSimplicialObject E).obj (op (⦋n⦌ : SimplexCategory))).I) :
    ((complexFunctor R E).map φ).f n ≫ Pi.π _ j =
      Pi.π _ j ≫
        (directImage R (((cechSimplicialObject E).obj
          (op (⦋n⦌ : SimplexCategory))).obj j).left).map φ :=
  Pi.map_π (fun i ↦ (directImage R (((cechSimplicialObject E).obj
    (op (⦋n⦌ : SimplexCategory))).obj i).left).map φ) j

/-- **The augmentation is natural in the sheaf of modules.** -/
theorem augmentation_naturality {F G : SheafOfModules.{u} R} (φ : F ⟶ G) :
    augmentation R E F ≫ ((complexFunctor R E).map φ).f 0 = φ ≫ augmentation R E G :=
  Pi.hom_ext _ _ fun j ↦
    (comp_comp_eq_of_comp_eq _ _ _ _ _ _ (map_f_comp_pi R E φ 0 j)
      (augmentation_comp_pi R E F j)).trans
      ((augmentationAt_naturality R φ _).trans
        ((congrArg (fun z ↦ φ ≫ z) (augmentation_comp_pi R E G j)).symm.trans
          (Category.assoc _ _ _).symm))

end Complex

section Single

variable {X : C} (E : PreZeroHypercover.{w} X)
  [HasProducts.{w} (SheafOfModules.{u} R)]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [HasZeroObject (SheafOfModules.{u} R)]

/-- **The augmentation as a morphism of cochain complexes `F[0] ⟶ Č(E, F)`**, out of the
complex concentrated in degree `0`.  This is the shape a resolution of `F` is given in: it is
a resolution exactly when this morphism is a quasi-isomorphism, which is not proved here. -/
noncomputable def augmentationHom (F : SheafOfModules.{u} R) :
    (CochainComplex.single₀ (SheafOfModules.{u} R)).obj F ⟶ (complexFunctor R E).obj F :=
  (CochainComplex.fromSingle₀Equiv _ F).symm ⟨augmentation R E F, augmentation_comp_d R E F⟩

/-- In degree `0`, `augmentationHom` is the augmentation. -/
theorem augmentationHom_f_zero (F : SheafOfModules.{u} R) :
    (augmentationHom R E F).f 0 = augmentation R E F :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- **The augmentation of the sheaf-level Čech complex, naturally in the sheaf of
modules**: a natural transformation from the degree-zero single-complex functor to
`Stacks.CechSite.SheafLevel.complexFunctor`. -/
noncomputable def augmentationNatTrans :
    CochainComplex.single₀ (SheafOfModules.{u} R) ⟶ complexFunctor R E where
  app F := augmentationHom R E F
  naturality F G φ := by
    refine (CochainComplex.fromSingle₀Equiv ((complexFunctor R E).obj G) F).injective
      (Subtype.ext ?_)
    change ((CochainComplex.single₀ _).map φ ≫ augmentationHom R E G).f 0 =
      (augmentationHom R E F ≫ (complexFunctor R E).map φ).f 0
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, augmentationHom_f_zero,
      augmentationHom_f_zero, CochainComplex.single₀_map_f_zero]
    exact (augmentation_naturality R E φ).symm

end Single

end Stacks.CechSite.SheafLevel

end
