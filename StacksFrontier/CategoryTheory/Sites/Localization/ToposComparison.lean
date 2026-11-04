module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import StacksFrontier.CategoryTheory.Sites.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# The localization of `Sh(C)` at `h_U^#` is the localization at `U`

Let `(C, J)` be a site and let `U` be an object of `C`.  Section 7.25 attaches to `U` the
localization morphism of topoi `j_U : Sh(C/U) ⟶ Sh(C)`, whose inverse image `j_U^{-1}` is
restriction to `C/U` (`GrothendieckTopology.overPullback`) and whose lower shriek `j_{U!}` is
`Functor.sheafPullback` along `Over.forget U`.  Section 7.30 attaches to the *sheaf* `F = h_U^#`
the localization morphism `j_F : Sh(C)/F ⟶ Sh(C)` of Stacks 04GZ
(`MorphismOfTopoi.overLocalization`), whose inverse image is `toOver F`, i.e. `H ↦ (H × F ⟶ F)`,
and whose lower shriek is the forgetful functor `Over.forget F`
(`MorphismOfTopoi.overLocalizationShriek`).

Stacks 04IQ asserts that these two morphisms of topoi agree, via the identification
`Sh(C/U) = Sh(C)/h_U^#` of Stacks 00Y1.  That identification is
`CategoryTheory.OverShriek.sheafEquivalence`, whose functor is `sheafFunctorToOver`, the sheaf
level `j_{U!}` viewed as a functor into the slice; **the direction used throughout this file is
the forward one**, `Φ_U := sheafFunctorToOver J : Sh(C/U) ⥤ Sh(C)/h_U^#`.  Every statement below
is an isomorphism of composites in which `Φ_U` appears, never `Φ_U^{-1}` alone, so no statement
depends on a choice of inverse:

* the lower shrieks agree as `Φ_U ⋙ j_{F!} ≅ j_{U!}`;
* the inverse images agree as `j_U^{-1} ⋙ Φ_U ≅ j_F^{-1}`;
* the pushforwards agree as `Φ_U ⋙ j_{F,*} ≅ j_{U,*}`.

`Φ_U` is an equivalence, hence both a left and a right adjoint of its inverse, so it is itself an
(iso)morphism of topoi `Sh(C/U) ⟶ Sh(C)/h_U^#`; `sheafSliceMorphismOfTopoi` records this, and
lets the three isomorphisms above be read as the single statement
`j_U = j_F ∘ sheafSliceMorphismOfTopoi`.

## Main results

* `CategoryTheory.OverShriek.sheafSliceMorphismOfTopoi`: Stacks 00Y1's equivalence as a morphism
  of topoi `Sh(C/U) ⟶ Sh(C)/h_U^#`.
* `CategoryTheory.OverShriek.sheafFunctorToOverCompForgetIso` (Stacks 04IQ): `j_{F!} ∘ Φ_U =
  j_{U!}`.
* `CategoryTheory.OverShriek.overPullbackCompSheafFunctorToOverIso` (Stacks 04IQ):
  `j_F^{-1} = j_U^{-1}`.
* `CategoryTheory.OverShriek.sheafFunctorToOverCompPushforwardIso` (Stacks 04IQ):
  `j_{F,*} = j_{U,*}`.

## What is not done

The assertion of Stacks 04GZ that `Sh(C)/F` is a topos is not formalized here.
-/

@[expose] public section

namespace CategoryTheory.OverShriek

open Limits Opposite MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] {U : C} (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
  [HasWeakSheafify (J.over U) (Type v)]
  [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

noncomputable section

/-- **Stacks 00Y1 as a morphism of topoi.**  The equivalence `Φ_U : Sh(C/U) ⥤ Sh(C)/h_U^#` of
Stacks 00Y1 is an isomorphism of topoi: its inverse is both a left and a right adjoint of it, and
being an equivalence it is left exact.

Taking `Φ_U` as the *pushforward* and its inverse as the *inverse image* is the convention forced
by `MorphismOfTopoi`, in which the inverse image runs against the direction of the morphism. -/
def sheafSliceMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (J.over U) (Type v))
      (Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) where
  pushforward := sheafFunctorToOver (U := U) J
  inverseImage := (sheafEquivalence (U := U) J).inverse
  adj := (sheafEquivalence (U := U) J).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := (sheafEquivalence (U := U) J).toAdjunction.rightAdjoint_preservesLimits
    ⟨fun _ _ _ => inferInstance⟩

/-- **Stacks 04IQ**, on lower shrieks: `j_{F!} ∘ Φ_U = j_{U!}` for `F = h_U^#`.

The lower shriek of the localization morphism `j_F` of Stacks 04GZ is the forgetful functor
`Over.forget F` (`MorphismOfTopoi.overLocalizationShriek`), so this says that the sheaf underlying
`Φ_U G` is `j_{U!}G`. -/
@[stacks 04IQ "j_{F!} = j_{U!} for F = h_U^#: the lower shrieks agree"]
def sheafFunctorToOverCompForgetIso :
    sheafFunctorToOver (U := U) J ⋙
        Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ≅
      (Over.forget U).sheafPullback (Type v) (J.over U) J :=
  sheafFunctorToOverForgetIso J

/-- `Φ_U^{-1} ⋙ j_{U!} ≅ Over.forget (h_U^#)`: the lower shriek identity of Stacks 04IQ read
through the inverse of the equivalence. -/
def inverseCompShriekIso :
    (sheafEquivalence (U := U) J).inverse ⋙
        (Over.forget U).sheafPullback (Type v) (J.over U) J ≅
      Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  Functor.isoWhiskerLeft _ (sheafFunctorToOverCompForgetIso J).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivalence (U := U) J).counitIso _ ≪≫
    Functor.leftUnitor _

/-- **Stacks 04IQ**, on inverse images: `j_F^{-1} = j_U^{-1}` for `F = h_U^#`, i.e.
`j_U^{-1} ⋙ Φ_U ≅ toOver F`. -/
@[stacks 04IQ "j_F^{-1} = j_U^{-1} for F = h_U^#: the inverse images agree"]
def overPullbackCompSheafFunctorToOverIso :
    J.overPullback (Type v) U ⋙ sheafFunctorToOver (U := U) J ≅
      toOver ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) :=
  Adjunction.rightAdjointUniq
    ((((sheafEquivalence (U := U) J).symm.toAdjunction).comp
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)).ofNatIsoLeft
      (inverseCompShriekIso J))
    (forgetAdjToOver _)

/-- The counit isomorphism `Φ_U^{-1} ⋙ Φ_U ≅ 𝟭` of the equivalence of Stacks 00Y1, with `Φ_U`
spelled as `sheafFunctorToOver`. -/
def counitIsoOfSheafFunctorToOver :
    (sheafEquivalence (U := U) J).inverse ⋙ sheafFunctorToOver (U := U) J ≅
      𝟭 (Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) :=
  (sheafEquivalence (U := U) J).counitIso

/-- The components of `inverseCompShriekIso`, in terms of `sheafFunctorToOverForgetIso` and the
counit of the equivalence. -/
theorem inverseCompShriekIso_hom_app (X : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) :
    (inverseCompShriekIso J).hom.app X =
      (sheafFunctorToOverForgetIso (U := U) J).inv.app
          ((sheafEquivalence (U := U) J).inverse.obj X) ≫
        (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map
          ((counitIsoOfSheafFunctorToOver J).hom.app X) := by
  dsimp [inverseCompShriekIso, sheafFunctorToOverCompForgetIso, counitIsoOfSheafFunctorToOver]
  rw [Category.id_comp]
  refine congrArg (fun z => (sheafFunctorToOverForgetIso (U := U) J).inv.app
    ((sheafEquivalence (U := U) J).inverse.obj X) ≫ z) ?_
  exact Category.comp_id _

/-- The inverse form of `inverseCompShriekIso_hom_app`. -/
theorem inverseCompShriekIso_inv_app (X : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U))) :
    (inverseCompShriekIso J).inv.app X =
      (Over.forget ((presheafToSheaf J (Type v)).obj (yoneda.obj U))).map
          ((counitIsoOfSheafFunctorToOver J).inv.app X) ≫
        (sheafFunctorToOverForgetIso (U := U) J).hom.app
          ((sheafEquivalence (U := U) J).inverse.obj X) := by
  refine Iso.inv_ext (f := (inverseCompShriekIso J).app X) ?_
  rw [Iso.app_hom, inverseCompShriekIso_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

/-- **Stacks 04IQ identifies the first projection with the counit of `j_{U!} ⊣ j_U^{-1}`.**

The isomorphism `j_U^{-1} ⋙ Φ_U ≅ toOver h_U^#` of Stacks 04IQ is a morphism of `Sh(C)/h_U^#`;
its underlying map followed by the projection `A ⊗ h_U^# ⟶ A` is, through Stacks 00Y1's
identification of the sheaf underlying `Φ_U G` with `j_{U!}G`, the counit of `j_{U!} ⊣ j_U^{-1}`.
-/
theorem left_overPullbackCompSheafFunctorToOverIso_hom_app_comp_fst (A : Sheaf J (Type v)) :
    ((overPullbackCompSheafFunctorToOverIso J).hom.app A).left ≫
        fst A ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) =
      (sheafFunctorToOverForgetIso (U := U) J).hom.app ((J.overPullback (Type v) U).obj A) ≫
        ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A := by
  have key : ((overPullbackCompSheafFunctorToOverIso J).hom.app A).left ≫
        fst A ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) =
      ((((sheafEquivalence (U := U) J).symm.toAdjunction).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J)).ofNatIsoLeft
        (inverseCompShriekIso J)).counit.app A := by
    rw [← forgetAdjToOver.homEquiv_symm]
    exact Adjunction.homEquiv_symm_rightAdjointUniq_hom_app _ _ A
  rw [key, Adjunction.ofNatIsoLeft_counit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_counit_app,
    inverseCompShriekIso_inv_app]
  slice_lhs 2 3 => rw [← NatTrans.naturality]
  slice_lhs 1 2 => rw [Functor.comp_map, ← Functor.map_comp]
  have htri : (counitIsoOfSheafFunctorToOver J).inv.app
        ((((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J) ⋙
          (sheafEquivalence (U := U) J).symm.inverse).obj A) ≫
      (sheafFunctorToOver (U := U) J).map
        (((sheafEquivalence (U := U) J).symm.toAdjunction).counit.app
          (((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).obj A)) = 𝟙 _ :=
    (sheafEquivalence (U := U) J).counitInv_functor_comp _
  rw [htri]
  simp only [Category.assoc]
  exact Category.id_comp ((sheafFunctorToOverForgetIso (U := U) J).hom.app
      (((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).obj A) ≫
    ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J).counit.app A)

/-- The inverse image identity of Stacks 04IQ read through the inverse of the equivalence:
`j_F^{-1} ⋙ Φ_U^{-1} ≅ j_U^{-1}`.  This is the form which says that the inverse image of the
composite morphism of topoi `j_F ∘ sheafSliceMorphismOfTopoi` is `j_U^{-1}`. -/
def toOverCompInverseIso :
    toOver ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⋙
        (sheafEquivalence (U := U) J).inverse ≅
      J.overPullback (Type v) U :=
  Functor.isoWhiskerRight (overPullbackCompSheafFunctorToOverIso J).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivalence (U := U) J).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **Stacks 04IQ**, on pushforwards: `j_{F,*} = j_{U,*}` for `F = h_U^#`, i.e.
`Φ_U ⋙ j_{F,*} ≅ j_{U,*}`.

Both pushforwards are taken as data, as in Stacks 04GZ, 04H0 and 04IR: `p` is a right adjoint of
`j_F^{-1} = toOver F` and `q` a right adjoint of `j_U^{-1}`. -/
@[stacks 04IQ "j_{F,*} = j_{U,*} for F = h_U^#: the pushforwards agree"]
def sheafFunctorToOverCompPushforwardIso
    {p : Over ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⥤ Sheaf J (Type v)}
    (adjp : toOver ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⊣ p)
    {q : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)}
    (adjq : J.overPullback (Type v) U ⊣ q) :
    sheafFunctorToOver (U := U) J ⋙ p ≅ q :=
  Functor.isoWhiskerLeft _
      (Adjunction.rightAdjointUniq
        (adjp.ofNatIsoLeft (overPullbackCompSheafFunctorToOverIso J).symm)
        (adjq.comp (sheafEquivalence (U := U) J).toAdjunction)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivalence (U := U) J).unitIso.symm q ≪≫
    Functor.leftUnitor _

end

end CategoryTheory.OverShriek
