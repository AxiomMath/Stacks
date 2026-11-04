module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekAssociativity
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtalePushforwardSquare

import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the proper-support direct image along a composite

Consider two cartesian squares of a big étale site on top of each other
```
X' --c--> X
|f'       |f
v         v
Y' --b--> Y
|g'       |g
v         v
Z' --a--> Z
```
with `f` and `g` separated and locally of finite type. Stacks, Remark 0F77 (2), asserts that the
base change isomorphisms `a⁻¹ (g ∘ f)_! ≅ (g' ∘ f')_! c⁻¹`, `a⁻¹ g_! ≅ g'_! b⁻¹` and
`b⁻¹ f_! ≅ f'_! c⁻¹` of Stacks 0F55 are compatible with the composition isomorphisms
`(g ∘ f)_! ≅ g_! ∘ f_!` and `(g' ∘ f')_! ≅ g'_! ∘ f'_!` of Stacks 0F50. The source's proof:
the isomorphisms of Stacks 0F55 and 0F50 are restrictions of the corresponding maps of ordinary
direct images, and for those the compatibility is the pasting of base change maps of
Sites, Remark 0F6X.

This file proves exactly that. The base change maps of Stacks 0F55 are
`AlgebraicGeometry.SmallEtale.properSupportBaseChange`, the restrictions of the pullback maps
`AlgebraicGeometry.SmallEtale.directImageBaseChange` of ordinary direct images; the latter are
identified with the mates `AlgebraicGeometry.smallEtalePushforwardBaseChange` of the
identifications of composite direct images, whose pasting is
`AlgebraicGeometry.smallEtalePushforwardBaseChange_paste`.

Part (1) of Remark 0F77, the associativity of the composition isomorphisms, is
`AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso_assoc`.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardBaseChange_app_eq`: the pullback map of
  Sites 06UM is the mate of the identification of the two composite direct images.
* `AlgebraicGeometry.SmallEtale.properSupport_baseChange_paste_app` and
  `AlgebraicGeometry.SmallEtale.properSupport_baseChange_compIso_app`: the compatibility for any
  maps restricting the base change maps of ordinary direct images.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChange_compIso`: **Stacks, Remark 0F77 (2)**.

## References

* [Stacks Project, Tag 0F77](https://stacks.math.columbia.edu/tag/0F77)
* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F6X](https://stacks.math.columbia.edu/tag/0F6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' Z' : B.Scheme}
  (c : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (a : Z' ⟶ Z)

/-- Moving two isomorphisms across an equation: if `F i ≫ e = r ≫ j`, then
`e ≫ j⁻¹ = F i⁻¹ ≫ r`. -/
private lemma comp_inv_eq_map_inv_comp_of_map_hom_comp {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {P Q : C} {R S : D} (i : P ≅ Q) (j : R ≅ S) (e : G.obj Q ⟶ S)
    (r : G.obj P ⟶ R) (h : G.map i.hom ≫ e = r ≫ j.hom) :
    e ≫ j.inv = G.map i.inv ≫ r := by
  rw [Iso.comp_inv_eq, ← cancel_epi (G.map i.hom), h]
  simp [← G.map_comp_assoc]

section BaseChangeMap

variable {X₀ Y₀ X₀' Y₀' : B.Scheme} (p : X₀' ⟶ X₀) (q' : X₀' ⟶ Y₀') (q : X₀ ⟶ Y₀)
  (r : Y₀' ⟶ Y₀) (sq : IsPullback p q' q r)

/-- The comparison `X'_{V'} ⟶ p⁻¹(X_V)` used to pull sections back is the comparison of the two
iterated base changes around the square through the base change along the common composite. -/
theorem fiberBaseChangeArrow_eq (V : SmallEtale B Y₀.obj Y₀.property) :
    fiberBaseChangeArrow B p q' q r sq V =
      (smallEtaleBaseChange_compIso B X₀' Y₀' Y₀ q' r).val.hom.app V ≫
        (eqToHom (congrArg (smallEtaleBaseChange B) sq.w.symm)).app V ≫
        (smallEtaleBaseChange_compIso B X₀' X₀ Y₀ p q).val.inv.app V := by
  have h₁ := fiberBaseChangeArrow_proj B p q' q r sq V
  have h₂ := fiberBaseChangeMap_fst B p q' q r sq V
  rw [← h₁, Category.assoc] at h₂
  exact smallEtaleBaseChange_square_eq B p q' q r sq.w V _ h₂

/-- The pullback map `r⁻¹ q_* ⟶ q'_* p⁻¹` of Sites 06UM, defined by pulling sections back, is the
base change map of the square, the mate of the identification of the two composite direct
images. -/
theorem smallEtalePushforwardBaseChange_app_eq (F : AbelianSheaf.{u, v} B X₀) :
    (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} p q' q r sq.w).app F =
      directImageBaseChange.{u, v} B p q' q r sq F := by
  apply ((B.smallPullbackAdjunction r AddCommGrpCat.{max (u + 1) v}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine (unit_mateEquiv_symm (B.smallPullbackAdjunction p AddCommGrpCat.{max (u + 1) v})
    (B.smallPullbackAdjunction r AddCommGrpCat.{max (u + 1) v})
    (smallEtalePushforwardSquare B AddCommGrpCat.{max (u + 1) v} p q' q r sq.w) F).symm.trans
    (Eq.trans ?_ (directImageBaseChange_triangle.{u, v} B p q' q r sq F).symm)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  rw [show (directImageBaseChangePushforward.{u, v} B p q' q r sq F).hom.app V =
    directImageBaseChangeApp.{u, v} B p q' q r sq F V.unop from rfl]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app, smallEtalePushforwardSquare_app_hom_app,
    directImageBaseChangeApp, pullbackSectionAlongHom, fiberBaseChangeArrow_eq]
  rfl

end BaseChangeMap

/-- The inclusion of the proper-support direct image into the ordinary direct image is a
monomorphism. -/
instance mono_properSupportToPushforward_app {S T : B.Scheme} (k : S ⟶ T)
    [LocallyOfFiniteType (B.inclusion.map k)] (F : AbelianSheaf.{u, v} B S) :
    Mono ((properSupportToPushforward.{u, max (u + 1) v} B k).app F) :=
  inferInstanceAs (Mono (fShriekSubsheaf B k F).val.arrow)

/-- The composition isomorphism of Stacks 0F50 is the restriction of the comparison of ordinary
direct images. -/
@[sga "4 XVII 6.1.3" "partial"]
theorem properSupportFunctor_compIso_hom_app_comp [LocallyOfFiniteType (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map g)] [IsSeparated (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g)] (F : AbelianSheaf.{u, v} B X) :
    letI := locallyOfFiniteType_map_comp B f g
    (properSupportFunctor_compIso.{u, max (u + 1) v} B f g).val.hom.app F ≫
        (properSupportToPushforward B (f ≫ g)).app F =
      (properSupportToPushforward B g).app ((properSupportFunctor B f).obj F) ≫
        (B.smallPushforward g AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B f).app F) ≫
        (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{max (u + 1) v}).hom.app
          F := by
  let := locallyOfFiniteType_map_comp B f g
  have he := congrArg Iso.hom ((properSupportFunctor_compIso.{u, max (u + 1) v} B f g).property F)
  rw [Iso.app_hom] at he
  rw [he]
  exact (properSupportSheaf_compIso.{u, max (u + 1) v} B f g F).property

/-- **The compatibility of Stacks, Remark 0F77 (2), forward form.** For two cartesian squares on
top of each other with `f` and `g` separated and locally of finite type, let `ε₁`, `ε₂` and `ε` be
maps `b⁻¹ f_! ⟶ f'_! c⁻¹`, `a⁻¹ g_! ⟶ g'_! b⁻¹` and `a⁻¹ (g ∘ f)_! ⟶ (g' ∘ f')_! c⁻¹` which
restrict the base change maps of ordinary direct images (the defining property of the
isomorphisms of Stacks 0F55). Then `a⁻¹` of the composition isomorphism of Stacks 0F50 followed
by `ε` is `ε₂` followed by `g'_! ε₁` and the composition isomorphism for `f'` and `g'`. The
hypotheses on `f'`, `g'` and the composites hold automatically (base change and composition),
and are taken as instance arguments. -/
theorem properSupport_baseChange_paste_app (sq₁ : IsPullback c f' f b)
    (sq₂ : IsPullback b g' g a)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map f')] [LocallyOfFiniteType (B.inclusion.map g')]
    [LocallyOfFiniteType (B.inclusion.map (f ≫ g))]
    [LocallyOfFiniteType (B.inclusion.map (f' ≫ g'))]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map f')] [IsSeparated (B.inclusion.map g')]
    (ε₁ : ∀ F : AbelianSheaf.{u, v} B X,
      (B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B f).obj F) ⟶
        (properSupportFunctor B f').obj
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F))
    (ε₂ : ∀ F : AbelianSheaf.{u, v} B Y,
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B g).obj F) ⟶
        (properSupportFunctor B g').obj
          ((B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj F))
    (ε : ∀ F : AbelianSheaf.{u, v} B X,
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B (f ≫ g)).obj F) ⟶
        (properSupportFunctor B (f' ≫ g')).obj
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F))
    (hε₁ : ∀ F, ε₁ F ≫ (properSupportToPushforward B f').app
        ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B f).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c f' f b sq₁.w).app F)
    (hε₂ : ∀ F, ε₂ F ≫ (properSupportToPushforward B g').app
        ((B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B g).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} b g' g a sq₂.w).app F)
    (hε : ∀ F, ε F ≫
        (properSupportToPushforward B (f' ≫ g')).app
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B (f ≫ g)).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c (f' ≫ g') (f ≫ g) a
          (sq₁.paste_vert sq₂).w).app F)
    (F : AbelianSheaf.{u, v} B X) :
    (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
        ((properSupportFunctor_compIso B f g).val.hom.app F) ≫ ε F =
      ε₂ ((properSupportFunctor B f).obj F) ≫ (properSupportFunctor B g').map (ε₁ F) ≫
        (properSupportFunctor_compIso B f' g').val.hom.app
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) :=
  subfunctor_baseChange_paste_app
    (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{max (u + 1) v})
    (smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' AddCommGrpCat.{max (u + 1) v})
    (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c f' f b sq₁.w)
    (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} b g' g a sq₂.w)
    (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c (f' ≫ g') (f ≫ g) a
      (sq₁.paste_vert sq₂).w)
    (smallEtalePushforwardBaseChange_paste B AddCommGrpCat.{max (u + 1) v} c f' f b g' g a
      sq₁.w sq₂.w (sq₁.paste_vert sq₂).w)
    (properSupportToPushforward B f) (properSupportToPushforward B g)
    (properSupportToPushforward B (f ≫ g)) (properSupportToPushforward B f')
    (properSupportToPushforward B g') (properSupportToPushforward B (f' ≫ g'))
    (fun F => (properSupportFunctor_compIso B f g).val.hom.app F)
    (fun F => (properSupportFunctor_compIso B f' g').val.hom.app F)
    (properSupportFunctor_compIso_hom_app_comp B f g)
    (properSupportFunctor_compIso_hom_app_comp B f' g') ε₁ ε₂ ε hε₁ hε₂ hε F

/-- **Stacks, Remark 0F77 (2)**, in the orientation of the source's diagram: for maps `ε₁`,
`ε₂`, `ε` restricting the base change maps of ordinary direct images, as the isomorphisms of
Stacks 0F55 do, the square
```
a⁻¹ (g ∘ f)_! ---------------ε---------------> (g' ∘ f')_! c⁻¹
     |                                               |
a⁻¹ g_! f_! --ε₂--> g'_! b⁻¹ f_! --g'_! ε₁--> g'_! f'_! c⁻¹
```
whose vertical arrows are the composition isomorphisms of Stacks 0F50, commutes. -/
theorem properSupport_baseChange_compIso_app (sq₁ : IsPullback c f' f b)
    (sq₂ : IsPullback b g' g a)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map f')] [LocallyOfFiniteType (B.inclusion.map g')]
    [LocallyOfFiniteType (B.inclusion.map (f ≫ g))]
    [LocallyOfFiniteType (B.inclusion.map (f' ≫ g'))]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map f')] [IsSeparated (B.inclusion.map g')]
    (ε₁ : ∀ F : AbelianSheaf.{u, v} B X,
      (B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B f).obj F) ⟶
        (properSupportFunctor B f').obj
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F))
    (ε₂ : ∀ F : AbelianSheaf.{u, v} B Y,
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B g).obj F) ⟶
        (properSupportFunctor B g').obj
          ((B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj F))
    (ε : ∀ F : AbelianSheaf.{u, v} B X,
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).obj
          ((properSupportFunctor B (f ≫ g)).obj F) ⟶
        (properSupportFunctor B (f' ≫ g')).obj
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F))
    (hε₁ : ∀ F, ε₁ F ≫ (properSupportToPushforward B f').app
        ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B f).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c f' f b sq₁.w).app F)
    (hε₂ : ∀ F, ε₂ F ≫ (properSupportToPushforward B g').app
        ((B.smallInverseImage b AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B g).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} b g' g a sq₂.w).app F)
    (hε : ∀ F, ε F ≫
        (properSupportToPushforward B (f' ≫ g')).app
          ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportToPushforward B (f ≫ g)).app F) ≫
        (smallEtalePushforwardBaseChange B AddCommGrpCat.{max (u + 1) v} c (f' ≫ g') (f ≫ g) a
          (sq₁.paste_vert sq₂).w).app F)
    (F : AbelianSheaf.{u, v} B X) :
    ε F ≫ (properSupportFunctor_compIso B f' g').val.inv.app
        ((B.smallInverseImage c AddCommGrpCat.{max (u + 1) v}).obj F) =
      (B.smallInverseImage a AddCommGrpCat.{max (u + 1) v}).map
          ((properSupportFunctor_compIso B f g).val.inv.app F) ≫
        ε₂ ((properSupportFunctor B f).obj F) ≫ (properSupportFunctor B g').map (ε₁ F) := by
  have hP :=
    properSupport_baseChange_paste_app B c f' f b g' g a sq₁ sq₂ ε₁ ε₂ ε hε₁ hε₂ hε F
  exact comp_inv_eq_map_inv_comp_of_map_hom_comp _
    ((properSupportFunctor_compIso B f g).val.app F)
    ((properSupportFunctor_compIso B f' g').val.app ((B.smallInverseImage c _).obj F)) _ _ hP

/-- **Stacks, Remark 0F77, part (2).** Let
```
X' --c--> X
|f'       |f
v         v
Y' --b--> Y
|g'       |g
v         v
Z' --a--> Z
```
be two cartesian squares of a big étale site, with `f` and `g` separated and locally of finite
type. Then the square
```
a⁻¹ (g ∘ f)_! ------------------------------> (g' ∘ f')_! c⁻¹
     |                                               |
a⁻¹ g_! f_! ------> g'_! b⁻¹ f_! ------> g'_! f'_! c⁻¹
```
of abelian sheaves on the small étale site of `Z'` commutes, where the horizontal arrows are the
base change maps of Stacks 0F55 (`AlgebraicGeometry.SmallEtale.properSupportBaseChange`) for the
rectangle, for the lower square at `f_! F`, and `g'_!` of that for the upper square, and the
vertical arrows are the composition isomorphisms of Stacks 0F50
(`AlgebraicGeometry.SmallEtale.properSupportFunctor_compIso`). -/
@[stacks 0F77 "part (2): compatibility of the base change maps of 0F55 with the composition \
isomorphisms of 0F50"]
theorem properSupportBaseChange_compIso (sq₁ : IsPullback c f' f b)
    (sq₂ : IsPullback b g' g a)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)]
    (F : AbelianSheaf.{u, v} B X) :
    letI : LocallyOfFiniteType (B.inclusion.map f') :=
      MorphismProperty.of_isPullback (sq₁.map B.inclusion) inferInstance
    letI : LocallyOfFiniteType (B.inclusion.map g') :=
      MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
    letI : IsSeparated (B.inclusion.map f') :=
      MorphismProperty.of_isPullback (sq₁.map B.inclusion) inferInstance
    letI : IsSeparated (B.inclusion.map g') :=
      MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
    letI := locallyOfFiniteType_map_comp B f g
    letI := locallyOfFiniteType_map_comp B f' g'
    properSupportBaseChange.{u, v} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂) F ≫
        (properSupportFunctor_compIso B f' g').val.inv.app ((abPullback.{u, v} B c).obj F) =
      (abPullback.{u, v} B a).map ((properSupportFunctor_compIso B f g).val.inv.app F) ≫
        properSupportBaseChange.{u, v} B b g' g a sq₂ ((properSupportFunctor B f).obj F) ≫
        (properSupportFunctor B g').map (properSupportBaseChange.{u, v} B c f' f b sq₁ F) := by
  let : LocallyOfFiniteType (B.inclusion.map f') :=
    MorphismProperty.of_isPullback (sq₁.map B.inclusion) inferInstance
  let : LocallyOfFiniteType (B.inclusion.map g') :=
    MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
  let : IsSeparated (B.inclusion.map f') :=
    MorphismProperty.of_isPullback (sq₁.map B.inclusion) inferInstance
  let : IsSeparated (B.inclusion.map g') :=
    MorphismProperty.of_isPullback (sq₂.map B.inclusion) inferInstance
  let := locallyOfFiniteType_map_comp B f g
  let := locallyOfFiniteType_map_comp B f' g'
  refine properSupport_baseChange_compIso_app B c f' f b g' g a sq₁ sq₂
    (properSupportBaseChange.{u, v} B c f' f b sq₁)
    (properSupportBaseChange.{u, v} B b g' g a sq₂)
    (properSupportBaseChange.{u, v} B c (f' ≫ g') (f ≫ g) a (sq₁.paste_vert sq₂))
    (fun F => ?_) (fun F => ?_) (fun F => ?_) F <;>
  (rw [smallEtalePushforwardBaseChange_app_eq]
   exact properSupportBaseChange_comp_arrow.{u, v} B _ _ _ _ _ _)

end AlgebraicGeometry.SmallEtale
