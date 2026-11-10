module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

/-!
# Transferring the base change comparison between the two presentations of the small étale site

Let `B` be a big étale site and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a commutative square of its underlying category. Each of the four schemes carries two small
étale sites: the size-bounded site `AlgebraicGeometry.SmallEtale` of Stacks 021B, and Mathlib's
site `AlgebraicGeometry.Scheme.Etale` of *all* schemes étale over the base. The two have the
same sheaves, by `AlgebraicGeometry.SmallEtale.sheafEquiv`, and each carries a base change
comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for the square. The identification of a finite direct image
with its base change, Stacks 0959, is proved for the **bounded** presentation, as
`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans`; the proper base change development works
on **Mathlib's**. This file moves the invertibility from the one to the other.

The device is `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`: a mate
transports along a change of the four categories of its square, provided the four comparisons
filling the sides of the resulting cube are invertible and the 2-cells `β`, `β'` between the
composites of right adjoints correspond. The four side comparisons are already available — the
two through the inverse images are
`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChange`, and the two through the direct
images are `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` — so what is
needed is the correspondence of `β` and `β'`, and that is the content of
`AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq` below.

**What this file does not do.** The transfer here is at the coefficient category at which
Stacks 0959 is stated, namely sheaves of sets. The proper base change development needs it for
sheaves of abelian groups, and crossing from the one to the other is a second application of
the same transport, along `CategoryTheory.sheafCompose` for the forgetful functor; that step is
not carried out here. Consequently **nothing in this file is tagged 0A4E**: the one input of
Stacks 0A4E that
`Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso` carries
as a hypothesis is still carried.

## Main definitions

* `AlgebraicGeometry.SmallEtale.unboundedPushforward` — direct image of sheaves on Mathlib's
  small étale site, along a morphism of the underlying category of a big étale site.
* `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` and
  `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate` — the comparison of the two composite
  direct images around the square, on Mathlib's site and on the bounded site, at an arbitrary
  coefficient category and with the diagonal of the square carried as a named morphism.

## Main results

* `AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq` — **the cube identity.** The bounded
  comparison of composite direct images, pasted with the comparisons of the two presentations,
  is the comparison on Mathlib's site. This is the sheaf-level form of the identity of *sites*
  `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_square`.
* `AlgebraicGeometry.SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate` — the 2-cell
  whose mate is the base change comparison of Stacks 0959 is
  `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`.
* `AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso` — **the
  transfer of invertibility onto Mathlib's presentation of the small étale site**: the base change
  comparison for sheaves of sets on Mathlib's small étale sites is invertible as soon as the one
  on the size-bounded site of Stacks 021B is. Nothing is assumed of the square.
* `AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate` — **Stacks 0959 on
  Mathlib's presentation of the small étale site**: the previous statement with the invertibility
  on the bounded site supplied by Stacks 0959, for a cartesian square with `f` finite.

## Implementation notes

**Everything is hand-associated in term mode.** `AlgebraicGeometry.Scheme.Etale` is
`CategoryTheory.MorphismProperty.Over` at `AlgebraicGeometry.Etale`, which is a family of
propositions rather than a term of `CategoryTheory.MorphismProperty`; a goal mentioning
morphisms of `Scheme.Etale` is therefore not type-correct at the transparency at which `rw` and
`simp` match, and neither tactic can so much as reassociate a composite there — nor cancel an
identity whose object is only definitionally the source of the morphism beside it. Every
reassociation and cancellation is consequently packaged as a `private` lemma stated for an
abstract category, where both tactics work, and applied to explicit arguments; this is the
`paste4`/`map3` discipline of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComposition`.

**How the cube identity is reduced to the identity of sites.** Both sides are natural
transformations between functors into a sheaf category, so they agree as soon as they agree at
every sheaf `F` and every object `U`. Each factor of each side is of the form
`F.obj.map ψ.op` for a morphism `ψ` of Mathlib's small étale site of `X'`: the comparison of
the two presentations is `CategoryTheory.Functor.sheafPushforwardContinuousIso`, whose component
is restriction along the comparison of the two site functors, and
`CategoryTheory.Functor.sheafPushforwardContinuousComp` is the identity. Composing the factors
leaves one application of `F.obj.map` to a composite of four morphisms of sites on each side,
and the identity between those two composites is
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_square` with three invertible
factors cancelled.

**The diagonal is carried as a named morphism.** A commutative square presents its diagonal as
two different composites, so the comparisons of a direct image along a composite with the
composite of the direct images are taken in the factored form, in which the composite is a named
morphism together with an equation naming it. The 2-cell of Stacks 0959 is built instead from
the written-out composite together with a transport along the commutativity of the square;
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate` identifies the
two.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite

universe v' u' u

namespace AlgebraicGeometry.SmallEtale

/-! ### Reassociation and cancellation, done where `rw` works -/

section Abstract

/-- Cancelling the images of the identities at both ends of a morphism. -/
private lemma mapid_comp_mapid {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞}
    (m : X ⟶ Y) : F.map (𝟙 X) ≫ F.map m ≫ F.map (𝟙 Y) = F.map m := by
  simp

/-- Cancelling the images of the identities at both ends of a morphism, left-bracketed. -/
private lemma mapid_comp_mapid' {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) {X Y : 𝒞}
    (m : X ⟶ Y) : (F.map (𝟙 X) ≫ F.map m) ≫ F.map (𝟙 Y) = F.map m := by
  simp

/-- Two images under a presheaf compose into the image of the composite. -/
private lemma map2_op {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞ᵒᵖ ⥤ 𝒟) {X Y Z : 𝒞}
    (a : Y ⟶ Z) (b : X ⟶ Y) : F.map a.op ≫ F.map b.op = F.map (b ≫ a).op := by
  rw [← F.map_comp, ← op_comp]

/-- Four images under a presheaf compose into the image of the composite. -/
private lemma map4_op {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞ᵒᵖ ⥤ 𝒟)
    {X₁ X₂ X₃ X₄ X₅ : 𝒞} (a : X₄ ⟶ X₅) (b : X₃ ⟶ X₄) (c : X₂ ⟶ X₃) (d : X₁ ⟶ X₂) :
    F.map a.op ≫ F.map b.op ≫ F.map c.op ≫ F.map d.op = F.map (d ≫ c ≫ b ≫ a).op := by
  simp only [← F.map_comp, ← op_comp, Category.assoc]

/-- The image under a functor of the unit of an isomorphism of functors. -/
private lemma map_hom_inv_id_app {𝒞 𝒟 ℰ : Type*} [Category* 𝒞] [Category* 𝒟] [Category* ℰ]
    (Fn : 𝒟 ⥤ ℰ) {G H : 𝒞 ⥤ 𝒟} (e : G ≅ H) (c : 𝒞) :
    Fn.map (e.hom.app c) ≫ Fn.map (e.inv.app c) = 𝟙 (Fn.obj (G.obj c)) := by
  rw [← Fn.map_comp, e.hom_inv_id_app, Fn.map_id]

/-- **The cancellation behind the cube identity.** Two fourfold composites with the same ends
agree; cancelling the last factor of the one and the first two factors of the other turns that
agreement into the identity between composites that the cube identity needs. The middle factor
`mid` of the conclusion is carried separately so that a consumer may supply it in whatever form
it has, here as the image of a composite under a functor. -/
private lemma cancel_square {𝒞 : Type*} [Category* 𝒞] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : 𝒞}
    (A₁ : O₁ ⟶ O₂) (A₂ : O₂ ⟶ O₃) (A₃ : O₃ ⟶ O₄) (A₄ : O₄ ⟶ O₅)
    (B₁ : O₁ ⟶ O₆) (B₂ : O₆ ⟶ O₇) (B₃ : O₇ ⟶ O₈) (B₄ : O₈ ⟶ O₅)
    (iA₄ : O₅ ⟶ O₄) (iB₁ : O₆ ⟶ O₁) (iB₂ : O₇ ⟶ O₆) (mid : O₆ ⟶ O₂)
    (hmid : mid = iB₁ ≫ A₁)
    (hA₄ : A₄ ≫ iA₄ = 𝟙 O₄) (hB₁ : iB₁ ≫ B₁ = 𝟙 O₆) (hB₂ : iB₂ ≫ B₂ = 𝟙 O₇)
    (S : A₁ ≫ A₂ ≫ A₃ ≫ A₄ = B₁ ≫ B₂ ≫ B₃ ≫ B₄) :
    iB₂ ≫ mid ≫ A₂ ≫ A₃ = B₃ ≫ B₄ ≫ iA₄ := by
  subst hmid
  have hA : A₁ ≫ A₂ ≫ A₃ = (B₁ ≫ B₂ ≫ B₃ ≫ B₄) ≫ iA₄ := by
    rw [← S]
    simp only [Category.assoc, hA₄, Category.comp_id]
  simp only [Category.assoc] at hA ⊢
  rw [hA, ← Category.assoc iB₁ B₁, hB₁, Category.id_comp, ← Category.assoc iB₂ B₂, hB₂,
    Category.id_comp]

end Abstract

section TwoSquares

variable {C₁ C₂ C₃ C₄ C₇ C₈ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₇] [Category* C₈]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {Bo : C₃ ⥤ C₄}

/-- The component of a vertical composition of 2-squares. Mathlib's
`CategoryTheory.Functor.whiskerRight_app` does not apply to a pasting of 2-squares, whose
implicit functor arguments are not determined by matching. -/
public lemma ts_vComp_app {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}
    (w : TwoSquare T L R Bo) (w' : TwoSquare Bo L' R'' B'') (c : C₁) :
    (w ≫ᵥ w').app c = R''.map (w.app c) ≫ w'.app (L.obj c) := by
  simp [TwoSquare.vComp]

/-- The component of a 2-square whiskered on the left. -/
public lemma ts_whiskerLeft_app {L' : C₁ ⥤ C₃} (w : TwoSquare T L R Bo) (α : L ⟶ L') (c : C₁) :
    (w.whiskerLeft α).app c = w.app c ≫ Bo.map (α.app c) := rfl

/-- The component of a 2-square whiskered on the right. -/
public lemma ts_whiskerRight_app {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' Bo) (α : R ⟶ R')
    (c : C₁) :
    (w.whiskerRight α).app c = α.app (T.obj c) ≫ w.app c := rfl

end TwoSquares

/-! ### Sections of the comparisons of direct images -/

section Sections

variable (A : Type u') [Category.{v'} A] {C D : Type*} [Category* C] [Category* D]

private lemma sheafHom_comp_app {J : GrothendieckTopology C} {F G H : Sheaf J A} (a : F ⟶ G)
    (b : G ⟶ H) (U : Cᵒᵖ) : (a ≫ b).hom.app U = a.hom.app U ≫ b.hom.app U := rfl

/-- A comparison of direct images coming from an isomorphism of the two functors of sites acts
on sections by restriction along that isomorphism. -/
private lemma iso_hom_app_hom_app {F F' : C ⥤ D} (e : F ≅ F') (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] [F'.IsContinuous J K]
    (M : Sheaf K A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousIso e A J K).hom.app M).hom.app U =
      M.obj.map (e.inv.app U.unop).op := rfl

/-- The inverse form of `AlgebraicGeometry.SmallEtale.iso_hom_app_hom_app`. -/
private lemma iso_inv_app_hom_app {F F' : C ⥤ D} (e : F ≅ F') (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] [F'.IsContinuous J K]
    (M : Sheaf K A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousIso e A J K).inv.app M).hom.app U =
      M.obj.map (e.hom.app U.unop).op := rfl

/-- Sections of a direct image are sections over the image of the object. -/
private lemma pushObj_map (Fs : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Fs.IsContinuous J K] (M : Sheaf K A) {Z W : C} (ψ : Z ⟶ W) :
    ((Fs.sheafPushforwardContinuous A J K).obj M).obj.map ψ.op = M.obj.map (Fs.map ψ).op := rfl

/-- Direct image acts on a morphism of sheaves by reindexing the object of the site. -/
private lemma push_map_hom_app (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] {M N : Sheaf K A} (η : M ⟶ N) (U : Cᵒᵖ) :
    ((F.sheafPushforwardContinuous A J K).map η).hom.app U =
      η.hom.app (op (F.obj U.unop)) := rfl

/-- The comparison of a direct image along a composite with the composite of the direct images
acts on sections by restriction along the comparison of the two functors of sites: the
identification of a composite of restrictions with the restriction along the composite is the
identity. -/
private lemma comp'_hom_app_hom_app {E : Type*} [Category* E] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
    [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
    (M : Sheaf L A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousComp' eFG A J K L).hom.app M).hom.app U =
      M.obj.map (eFG.inv.app U.unop).op :=
  Category.id_comp _

/-- The inverse form of `AlgebraicGeometry.SmallEtale.comp'_hom_app_hom_app`. -/
private lemma comp'_inv_app_hom_app {E : Type*} [Category* E] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG)
    [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
    (M : Sheaf L A) (U : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousComp' eFG A J K L).inv.app M).hom.app U =
      M.obj.map (eFG.hom.app U.unop).op :=
  Category.comp_id _

/-- Transporting the target of the comparison of two functors of sites along an equality
transports the comparison of the direct images along the corresponding equality. -/
private lemma comp'_trans_eqToIso {E : Type*} [Category* E] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : C ⥤ D} {G : D ⥤ E} {FG FG' : C ⥤ E} (eFG : F ⋙ G ≅ FG) (k : FG = FG')
    [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L] [FG'.IsContinuous J L]
    (kk : FG.sheafPushforwardContinuous A J L = FG'.sheafPushforwardContinuous A J L) :
    Functor.sheafPushforwardContinuousComp' (eFG ≪≫ eqToIso k) A J K L =
      Functor.sheafPushforwardContinuousComp' eFG A J K L ≪≫ eqToIso kk := by
  subst k
  simp

end Sections

/-! ### Sections of the comparison of the two presentations -/

section Presentations

variable (A : Type u') [Category.{v'} A] (B : BigEtaleSite.{u})

/-- The comparison of the two presentations acts on sections, and its inverse acts, by restriction
along the comparison of the two base changes of sites. -/
private lemma pushforwardBaseChangeIso_app_hom_app {S T : B.Scheme} (f : T ⟶ S)
    (M : Sheaf (Scheme.smallEtaleTopology T.obj) A) (U : SmallEtale B S.obj S.property) :
    ((toEtaleSitePushforwardBaseChangeIso B f A).hom.app M).hom.app (op U) =
      M.obj.map ((toEtaleSiteBaseChangeIso B f).hom.app U).op ∧
    ((toEtaleSitePushforwardBaseChangeIso B f A).inv.app M).hom.app (op U) =
      M.obj.map ((toEtaleSiteBaseChangeIso B f).inv.app U).op := by
  have hc : (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
    Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous (B.inclusion.map f)
  have hc1 : (toEtaleSite B S.obj S.property ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ S.obj.smallEtaleTopology _
  have hc2 : (AlgebraicGeometry.smallEtaleBaseChange B f ⋙
      toEtaleSite B T.obj T.property).IsContinuous
      (topology B S.obj S.property) T.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B T.obj T.property) _
  have key : toEtaleSitePushforwardBaseChangeIso B f A =
      Functor.sheafPushforwardContinuousComp' (F := toEtaleSite B S.obj S.property)
          (G := Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f))
          (Iso.refl _) A _ _ _ ≪≫
        Functor.sheafPushforwardContinuousIso (toEtaleSiteBaseChangeIso B f).symm A _ _ ≪≫
          (Functor.sheafPushforwardContinuousComp'
            (F := AlgebraicGeometry.smallEtaleBaseChange B f)
            (G := toEtaleSite B T.obj T.property) (Iso.refl _) A _ _ _).symm := rfl
  constructor
  · rw [key, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
      sheafHom_comp_app, sheafHom_comp_app, comp'_hom_app_hom_app, iso_hom_app_hom_app,
      Iso.symm_hom, comp'_inv_app_hom_app]
    simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Iso.symm_inv, unop_op, op_id]
    exact mapid_comp_mapid M.obj _
  · rw [key, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, NatTrans.comp_app,
      sheafHom_comp_app, sheafHom_comp_app, comp'_hom_app_hom_app, iso_inv_app_hom_app,
      comp'_inv_app_hom_app]
    simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app, Iso.symm_hom, unop_op, op_id]
    exact mapid_comp_mapid' M.obj _

/-- **The comparison of the two presentations acts on sections by restriction along the
comparison of the two base changes of sites.** The two identifications of a composite of
restrictions with the restriction along the composite that
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso` is built from are identities,
so only the comparison of the sites survives. -/
public theorem pushforwardBaseChangeIso_hom_app_hom_app {S T : B.Scheme} (f : T ⟶ S)
    (M : Sheaf (Scheme.smallEtaleTopology T.obj) A) (U : SmallEtale B S.obj S.property) :
    ((toEtaleSitePushforwardBaseChangeIso B f A).hom.app M).hom.app (op U) =
      M.obj.map ((toEtaleSiteBaseChangeIso B f).hom.app U).op :=
  (pushforwardBaseChangeIso_app_hom_app A B f M U).1

/-- The inverse form of
`AlgebraicGeometry.SmallEtale.pushforwardBaseChangeIso_hom_app_hom_app`. -/
public theorem pushforwardBaseChangeIso_inv_app_hom_app {S T : B.Scheme} (f : T ⟶ S)
    (M : Sheaf (Scheme.smallEtaleTopology T.obj) A) (U : SmallEtale B S.obj S.property) :
    ((toEtaleSitePushforwardBaseChangeIso B f A).inv.app M).hom.app (op U) =
      M.obj.map ((toEtaleSiteBaseChangeIso B f).inv.app U).op :=
  (pushforwardBaseChangeIso_app_hom_app A B f M U).2

end Presentations

/-! ### The two comparisons of composite direct images around a square -/

section Mates

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A]

/-- **Direct image of sheaves on Mathlib's small étale site**, along a morphism of the
underlying category of a big étale site.

`Stacks.EtaleCohomology.smallEtalePushforward` is the same functor for a morphism of schemes;
this spelling names the topologies on the small étale sites of `S.obj` and `T.obj` rather than
of `B.inclusion.obj S` and `B.inclusion.obj T`, which is the spelling the comparisons of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison` use. -/
public abbrev unboundedPushforward {S T : B.Scheme} (k : T ⟶ S) :
    Sheaf (Scheme.smallEtaleTopology T.obj) A ⥤ Sheaf (Scheme.smallEtaleTopology S.obj) A :=
  (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map k)).sheafPushforwardContinuous A
    S.obj.smallEtaleTopology T.obj.smallEtaleTopology

/-- The comparison of a direct image along a composite with the composite of the direct images,
on Mathlib's small étale site, with the composite carried as a named morphism. -/
public abbrev unboundedPushforwardCompIso {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (Q : Z ⟶ V) (hQ : k ≫ l = Q) :
    unboundedPushforward B A k ⋙ unboundedPushforward B A l ≅ unboundedPushforward B A Q :=
  Functor.sheafPushforwardContinuousComp'
    (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map k) (B.inclusion.map l)
      (B.inclusion.map Q) (congrArg B.inclusion.map hQ.symm)).symm A _ _ _

/-- The comparison of a direct image along a composite with the composite of the direct images,
on the bounded small étale site, with the composite carried as a named morphism. -/
public abbrev boundedPushforwardCompIso {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V) (Q : Z ⟶ V)
    (hQ : k ≫ l = Q) :
    B.smallPushforward k A ⋙ B.smallPushforward l A ≅ B.smallPushforward Q A :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_factoredCompIso B Z W V k l Q hQ) A _ _ _

variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

/-- **The comparison `(g')_* f_* ⟶ (f')_* g_* ` of the two composite direct images around a
commutative square, on Mathlib's small étale site**, through the direct image along the
diagonal `P`. Its mate along the two horizontal inverse-image/direct-image adjunctions is the
base change comparison. -/
public def unboundedBaseChangeMate :
    TwoSquare (unboundedPushforward B A g') (unboundedPushforward B A f')
      (unboundedPushforward B A f) (unboundedPushforward B A g) :=
  TwoSquare.mk _ _ _ _
    ((unboundedPushforwardCompIso B A g' f P hP₁).hom ≫
      (unboundedPushforwardCompIso B A f' g P hP₂).inv)

/-- **The comparison `(g')_* f_* ⟶ (f')_* g_* ` of the two composite direct images around a
commutative square, on the bounded small étale site**, through the direct image along the
diagonal `P`. For sheaves of sets it is `AlgebraicGeometry.smallEtaleBaseChangeMate`, by
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChangeMate_eq_boundedBaseChangeMate`. -/
public def boundedBaseChangeMate :
    TwoSquare (B.smallPushforward g' A) (B.smallPushforward f' A) (B.smallPushforward f A)
      (B.smallPushforward g A) :=
  TwoSquare.mk _ _ _ _
    ((boundedPushforwardCompIso B A g' f P hP₁).hom ≫
      (boundedPushforwardCompIso B A f' g P hP₂).inv)

/-- Sections of `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate`: restriction along the
two comparisons of base change along the diagonal with the composite of the base changes. -/
public theorem unboundedBaseChangeMate_app_hom_app
    (F : Sheaf (Scheme.smallEtaleTopology X'.obj) A) (U : Y.obj.Etale) :
    ((unboundedBaseChangeMate B A f g g' f' P hP₁ hP₂).app F).hom.app (op U) =
      F.obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map f')
              (B.inclusion.map g) (B.inclusion.map P)
              (congrArg B.inclusion.map hP₂.symm)).symm.hom.app U ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (B.inclusion.map g')
            (B.inclusion.map f) (B.inclusion.map P)
            (congrArg B.inclusion.map hP₁.symm)).symm.inv.app U).op := by
  have h1 : (unboundedBaseChangeMate B A f g g' f' P hP₁ hP₂).app F =
      (unboundedPushforwardCompIso B A g' f P hP₁).hom.app F ≫
        (unboundedPushforwardCompIso B A f' g P hP₂).inv.app F := rfl
  rw [h1, sheafHom_comp_app, comp'_hom_app_hom_app, comp'_inv_app_hom_app]
  exact map2_op F.obj _ _

/-- Sections of `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`: restriction along the two
comparisons of base change along the diagonal with the composite of the base changes. -/
public theorem boundedBaseChangeMate_app_hom_app
    (N : Sheaf (topology B X'.obj X'.property) A) (U : SmallEtale B Y.obj Y.property) :
    ((boundedBaseChangeMate B A f g g' f' P hP₁ hP₂).app N).hom.app (op U) =
      N.obj.map
        ((smallEtaleBaseChange_factoredCompIso B X' Y' Y f' g P hP₂).hom.app U ≫
          (smallEtaleBaseChange_factoredCompIso B X' X Y g' f P hP₁).inv.app U).op := by
  have h1 : (boundedBaseChangeMate B A f g g' f' P hP₁ hP₂).app N =
      (boundedPushforwardCompIso B A g' f P hP₁).hom.app N ≫
        (boundedPushforwardCompIso B A f' g P hP₂).inv.app N := rfl
  rw [h1, sheafHom_comp_app, comp'_hom_app_hom_app, comp'_inv_app_hom_app]
  exact map2_op N.obj _ _

end Mates

/-! ### The cube identity -/

section Cube

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A]
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
variable
  {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) A ⥤ Sheaf (Scheme.smallEtaleTopology Y'.obj) A}
  {LBg : Sheaf (topology B Y.obj Y.property) A ⥤ Sheaf (topology B Y'.obj Y'.property) A}
  {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) A ⥤ Sheaf (Scheme.smallEtaleTopology X'.obj) A}
  {LBg' : Sheaf (topology B X.obj X.property) A ⥤ Sheaf (topology B X'.obj X'.property) A}
  (adjUg : LUg ⊣ unboundedPushforward B A g) (adjBg : LBg ⊣ B.smallPushforward g A)
  (adjUg' : LUg' ⊣ unboundedPushforward B A g') (adjBg' : LBg' ⊣ B.smallPushforward g' A)

/-- **The cube identity: the two comparisons of composite direct images around a commutative
square correspond under the comparison of the two presentations of the small étale site.**

The bounded comparison `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`, pasted with the
comparison of inverse images along the restriction functors through the mate operation and
corrected at the two ends by the comparisons of direct images
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`, is the comparison
`AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` on Mathlib's site pasted with the same
comparison of inverse images for `g`.

This is exactly the hypothesis of
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`, and it is the sheaf-level form of the identity
of sites `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_square`: evaluated at a
sheaf and an object, each side is restriction of sections along one of the two composites of
site comparisons occurring there. -/
public theorem baseChangeMate_cube_eq :
    ((mateEquiv adjUg' adjBg' (restrictionPullbackBaseChange B A g' adjUg' adjBg') ≫ᵥ
        boundedBaseChangeMate B A f g g' f' P hP₁ hP₂).whiskerRight
          (toEtaleSitePushforwardBaseChangeIso B f A).hom).whiskerLeft
        (toEtaleSitePushforwardBaseChangeIso B f' A).inv =
      unboundedBaseChangeMate B A f g g' f' P hP₁ hP₂ ≫ᵥ
        mateEquiv adjUg adjBg (restrictionPullbackBaseChange B A g adjUg adjBg) := by
  refine NatTrans.ext (funext fun F => ?_)
  rw [ts_whiskerLeft_app, ts_whiskerRight_app, ts_vComp_app, ts_vComp_app,
    mateEquiv_restrictionPullbackBaseChange, mateEquiv_restrictionPullbackBaseChange]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun UU => ?_))
  obtain ⟨U⟩ := UU
  simp only [sheafHom_comp_app, push_map_hom_app, pushforwardBaseChangeIso_hom_app_hom_app,
    pushforwardBaseChangeIso_inv_app_hom_app, boundedBaseChangeMate_app_hom_app,
    unboundedBaseChangeMate_app_hom_app, pushObj_map, unop_op, Iso.symm_hom, Iso.symm_inv,
    Category.assoc]
  refine Eq.trans (map4_op F.obj _ _ _ _) (Eq.trans ?_ (map2_op F.obj _ _).symm)
  refine congrArg (fun z => F.obj.map (Quiver.Hom.op z)) ?_
  exact cancel_square (𝒞 := X'.obj.Etale)
    (hmid := (toEtaleSite B X'.obj X'.property).map_comp _ _)
    (hA₄ := Iso.inv_hom_id_app _ _)
    (hB₁ := map_hom_inv_id_app _ _ _)
    (hB₂ := Iso.inv_hom_id_app _ _)
    (S := toEtaleSiteBaseChangeIso_hom_app_square B f g g' f' P hP₁.symm hP₂.symm U)

end Cube

/-! ### Stacks 0959 on Mathlib's presentation of the small étale site -/

section Transfer

variable (B : BigEtaleSite.{u})
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The 2-cell whose mate is the base change comparison of Stacks 0959 is
`AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`.**
`AlgebraicGeometry.smallEtaleBaseChangeMate` is built from the comparisons at the written-out
composites `g' ≫ f` and `f' ≫ g` together with a transport along the commutativity of the square;
the form used here takes the diagonal as a named morphism, so that the transport sits inside the
two comparisons instead. -/
public theorem smallEtaleBaseChangeMate_eq_boundedBaseChangeMate (h : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P) :
    smallEtaleBaseChangeMate B g' f' f g h =
      boundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂ := by
  subst hP₂
  rw [boundedBaseChangeMate, boundedPushforwardCompIso, boundedPushforwardCompIso,
    smallEtaleBaseChange_factoredCompIso, smallEtaleBaseChange_factoredCompIso,
    comp'_trans_eqToIso (kk :=
      congrArg (fun m : X' ⟶ Y => B.smallPushforward m (Type (u + 1))) hP₁),
    comp'_trans_eqToIso (kk := rfl), smallEtaleBaseChangeMate,
    smallEtaleSheafPushforwardCompIso, smallEtaleSheafPushforwardCompIso]
  simp

/-- **Stacks 0959 on Mathlib's presentation of the small étale site.** Consider a cartesian
square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site with `f` finite, and a choice of left adjoints of
the direct images along base change by `g` and by `g'` for sheaves of sets on *Mathlib's* small
étale sites. Then the base change comparison `g⁻¹ f_* ⟶ (f')_* (g')⁻¹` for those sites — the
mate of `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` — is an isomorphism.

`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans` is the same statement for the
size-bounded small étale sites of Stacks 021B. The passage between the two is
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis is
`AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq`; the functor at the corner that has to
reflect isomorphisms is restriction along the embedding of the bounded site of `Y'`, which is
one half of the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
public theorem isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso (h : g' ≫ f = f' ≫ g)
    (hall : ∀ F, IsIso ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F))
    (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
    {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology Y'.obj) (Type (u + 1))}
    {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology X'.obj) (Type (u + 1))}
    (adjUg : LUg ⊣ unboundedPushforward B (Type (u + 1)) g)
    (adjUg' : LUg' ⊣ unboundedPushforward B (Type (u + 1)) g') :
    IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)) := by
  have hEq : ((toEtaleSite B Y'.obj Y'.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B Y'.obj Y'.property) Y'.obj.smallEtaleTopology).IsEquivalence :=
    (sheafEquiv B Y'.obj Y'.property (Type (u + 1))).isEquivalence_inverse
  have hb : IsIso ((mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
        (B.smallPullbackAdjunction g (Type (u + 1)))).symm
      (boundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)) := by
    have hiso : IsIso (smallEtaleBaseChangeNatTrans B g' f' f g h) :=
      NatIso.isIso_of_isIso_app _
    rw [← smallEtaleBaseChangeMate_eq_boundedBaseChangeMate B f g g' f' h P hP₁ hP₂]
    exact hiso
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    adjUg' adjUg (B.smallPullbackAdjunction g' (Type (u + 1)))
    (B.smallPullbackAdjunction g (Type (u + 1)))
    (restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg' _)
    (restrictionPullbackBaseChange B (Type (u + 1)) g adjUg _)
    (toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).hom
    (toEtaleSitePushforwardBaseChangeIso B f' (Type (u + 1))).inv
    (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)
    (boundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)
    (baseChangeMate_cube_eq B (Type (u + 1)) f g g' f' P hP₁ hP₂ adjUg _ adjUg' _)

/-- **Stacks 0959 on Mathlib's presentation of the small étale site**, for a cartesian square
with `f` finite: the case of
`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso` in which the
invertibility on the size-bounded site is `AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans`,
Stacks 0959 itself. -/
public theorem isIso_mateEquiv_symm_unboundedBaseChangeMate
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
    {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology Y'.obj) (Type (u + 1))}
    {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (u + 1)) ⥤
      Sheaf (Scheme.smallEtaleTopology X'.obj) (Type (u + 1))}
    (adjUg : LUg ⊣ unboundedPushforward B (Type (u + 1)) g)
    (adjUg' : LUg' ⊣ unboundedPushforward B (Type (u + 1)) g') :
    IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)) :=
  isIso_mateEquiv_symm_unboundedBaseChangeMate_of_isIso B f g g' f' h
    (fun F => isIso_smallEtaleBaseChangeNatTrans B g' f' f g sq h F) P hP₁ hP₂ adjUg adjUg'

end Transfer

end AlgebraicGeometry.SmallEtale

end
