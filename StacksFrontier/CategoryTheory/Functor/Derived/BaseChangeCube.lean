module

public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePasting
public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition

/-!
# Base change maps of right derived functors along a further change of base

Consider a square of functors
```
K₁ --Kt--> K₂
|          |
Ft'        Ft
v          v
K₃ --Lt--> K₄
```
between categories with localizations, together with a transformation (not necessarily an
isomorphism) `e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft`. Exactly as for `Stacks.DerivedBaseChange.squareMap`, the
universal property of `RF' ⋙ LD`, a right derived functor of `Ft' ⋙ Q₃ ⋙ LD`, produces a
transformation `LD ∘ RF' ⟶ RF ∘ KD`; `Stacks.DerivedBaseChange.squareMap` is the case of an
isomorphism (`Stacks.DerivedBaseChange.squareMap_eq_squareMapOfHom`). In the situation of
Étale Cohomology, Section 0EZQ, with `Ft'` and `Ft` direct images and `Kt`, `Lt` inverse images,
this is the derived base change map `b⁻¹ Rf_* ⟶ Rf₁_* a⁻¹` of Cohomology on Sites, Remark 07A7.

The main result, `Stacks.DerivedBaseChange.squareMapOfHom_cube`, is the formal half of
[Stacks, Tag 0F7F]: given a cube whose four vertical faces carry such transformations, two of them
(`e`, `e₁`) for the top and bottom faces and two (`β`, `β'`) for the faces along the direct images,
and given transformations `SL`, `SK` of derived functors lifting transformations `σL`, `σK` of the
remaining two faces, the two composites around the induced cube of derived functors agree as soon
as the underived cube commutes.

## Main definitions

* `Stacks.DerivedBaseChange.squareMapOfHom`: the base change map of a square carrying a
  transformation.
* `Stacks.DerivedBaseChange.homotopySquareHom`: a transformation of a square of additive functors,
  on homotopy categories.

## Main results

* `Stacks.DerivedBaseChange.squareMapOfHom_fac_app`: the characterizing property.
* `Stacks.DerivedBaseChange.squareMapOfHom_cube`: compatibility with a further change of base.

## References

* [Stacks Project, Tag 0F7F](https://stacks.math.columbia.edu/tag/0F7F)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedBaseChange

section SquareOfHom

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄}
  {Kt : K₁ ⥤ K₂} {KD : D₁ ⥤ D₂} {Lt : K₃ ⥤ K₄} {LD : D₃ ⥤ D₄}
  {Ft' : K₁ ⥤ K₃} {RF' : D₁ ⥤ D₃} {Ft : K₂ ⥤ K₄} {RF : D₂ ⥤ D₄}

/-- The transformation out of `Ft' ⋙ Q₃ ⋙ LD` which the base change map of a square carrying a
transformation `e` extends: `LD (Ft' X) ≅ Lt (Ft' X) ⟶ Ft (Kt X) ⟶ RF (Kt X) ≅ RF (KD X)`. -/
def squareMapUnitOfHom (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft) :
    (Ft' ⋙ Q₃) ⋙ LD ⟶ Q₁ ⋙ KD ⋙ RF :=
  (Functor.associator Ft' Q₃ LD).hom ≫ Functor.whiskerLeft Ft' φL.hom ≫
    (Functor.associator Ft' Lt Q₄).inv ≫ Functor.whiskerRight e Q₄ ≫
    (Functor.associator Kt Ft Q₄).hom ≫ Functor.whiskerLeft Kt α ≫
    (Functor.associator Kt Q₂ RF).inv ≫ Functor.whiskerRight φK.inv RF ≫
    (Functor.associator Q₁ KD RF).hom

/-- The component of `squareMapUnitOfHom` at `X` is the composite
`φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.app X) ≫ α.app (Kt.obj X) ≫ RF.map (φK.inv.app X)`. -/
@[simp]
lemma squareMapUnitOfHom_app (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft) (X : K₁) :
    (squareMapUnitOfHom φK φL α e).app X =
      φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.app X) ≫ α.app (Kt.obj X) ≫
        RF.map (φK.inv.app X) := by
  simp [squareMapUnitOfHom]

variable (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]

/-- **The base change map of a square carrying a transformation.** For a transformation
`e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft`, with `KD` and `LD` induced by `Kt` and `Lt`, and right derived functors
`RF'` of `Ft'` and `RF` of `Ft`, this is the transformation `LD ∘ RF' ⟶ RF ∘ KD` characterized by
`squareMapOfHom_fac_app`. For `Ft'`, `Ft` direct images and `Kt`, `Lt` inverse images it is the
derived base change map of Cohomology on Sites, Remark 07A7. -/
def squareMapOfHom (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft)
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit α' LD) W₁] :
    RF' ⋙ LD ⟶ KD ⋙ RF :=
  (RF' ⋙ LD).rightDerivedDesc (whiskerUnit α' LD) W₁ (KD ⋙ RF) (squareMapUnitOfHom φK φL α e)

/-- The base change map of a square, precomposed with the unit of `RF'`, is the composite
`LD (Ft' X) ≅ Lt (Ft' X) ⟶ Ft (Kt X) ⟶ RF (Kt X) ≅ RF (KD X)`. -/
@[reassoc]
lemma squareMapOfHom_fac_app (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft)
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit α' LD) W₁] (X : K₁) :
    LD.map (α'.app X) ≫ (squareMapOfHom W₁ φK φL α' α e).app (Q₁.obj X) =
      φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.app X) ≫ α.app (Kt.obj X) ≫
        RF.map (φK.inv.app X) := by
  have h := (RF' ⋙ LD).rightDerived_fac_app (whiskerUnit α' LD) W₁ (KD ⋙ RF)
    (squareMapUnitOfHom φK φL α e) X
  simp only [whiskerUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, squareMapUnitOfHom_app] at h
  exact h

/-- The base change map of a square carrying an isomorphism is the base change map of the
underlying transformation. -/
lemma squareMap_eq_squareMapOfHom (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ≅ Kt ⋙ Ft)
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit α' LD) W₁] :
    squareMap W₁ φK φL α' α e = squareMapOfHom W₁ φK φL α' α e.hom :=
  rfl

end SquareOfHom

section Cube

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {K₅ : Type*} [Category* K₅] {K₆ : Type*} [Category* K₆]
  {K₇ : Type*} [Category* K₇] {K₈ : Type*} [Category* K₈]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {D₅ : Type*} [Category* D₅] {D₆ : Type*} [Category* D₆]
  {D₇ : Type*} [Category* D₇] {D₈ : Type*} [Category* D₈]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄}
  {Q₅ : K₅ ⥤ D₅} {Q₆ : K₆ ⥤ D₆} {Q₇ : K₇ ⥤ D₇} {Q₈ : K₈ ⥤ D₈}
  {Kt : K₁ ⥤ K₂} {KD : D₁ ⥤ D₂} {Lt : K₃ ⥤ K₄} {LD : D₃ ⥤ D₄}
  {K₁t : K₅ ⥤ K₆} {K₁D : D₅ ⥤ D₆} {L₁t : K₇ ⥤ K₈} {L₁D : D₇ ⥤ D₈}
  {At' : K₁ ⥤ K₅} {AD' : D₁ ⥤ D₅} {At : K₂ ⥤ K₆} {AD : D₂ ⥤ D₆}
  {Bt' : K₃ ⥤ K₇} {BD' : D₃ ⥤ D₇} {Bt : K₄ ⥤ K₈} {BD : D₄ ⥤ D₈}
  {Ft' : K₁ ⥤ K₃} {RF' : D₁ ⥤ D₃} {Ft : K₂ ⥤ K₄} {RF : D₂ ⥤ D₄}
  {Ft'₁ : K₅ ⥤ K₇} {RF'₁ : D₅ ⥤ D₇} {Ft₁ : K₆ ⥤ K₈} {RF₁ : D₆ ⥤ D₈}
  (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]
  (W₂ : MorphismProperty K₂) [Q₂.IsLocalization W₂]
  (W₅ : MorphismProperty K₅) [Q₅.IsLocalization W₅]

/-- **Compatibility of base change maps with a further change of base, formally.** Consider a cube
of functors with top face `Kt, Lt` over the direct images `Ft', Ft`, bottom face `K₁t, L₁t` over
`Ft'₁, Ft₁`, and the changes of base `At', At, Bt', Bt` from top to bottom, together with
transformations `e`, `e₁` of the top and bottom faces, `β`, `β'` of the faces along the direct
images, `σL`, `σK` of the two remaining faces, and transformations `SL`, `SK` of derived functors
lifting `σL` and `σK` (the hypotheses `hSL`, `hSK`). If the underived cube commutes (`hcube`),
then so does the derived one: at every `K`, the base change map of the top face followed by that of
the face of `Ft` and by `SK` equals `SL` followed by the base change map of the face of `Ft'` and
that of the bottom face. -/
theorem squareMapOfHom_cube
    (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (φK₁ : Q₅ ⋙ K₁D ≅ K₁t ⋙ Q₆) (φL₁ : Q₇ ⋙ L₁D ≅ L₁t ⋙ Q₈)
    (φA' : Q₁ ⋙ AD' ≅ At' ⋙ Q₅) (φA : Q₂ ⋙ AD ≅ At ⋙ Q₆)
    (φB' : Q₃ ⋙ BD' ≅ Bt' ⋙ Q₇) (φB : Q₄ ⋙ BD ≅ Bt ⋙ Q₈)
    (αF' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (αF : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF)
    (αF'₁ : Ft'₁ ⋙ Q₇ ⟶ Q₅ ⋙ RF'₁) (αF₁ : Ft₁ ⋙ Q₈ ⟶ Q₆ ⋙ RF₁)
    (e : Ft' ⋙ Lt ⟶ Kt ⋙ Ft) (e₁ : Ft'₁ ⋙ L₁t ⟶ K₁t ⋙ Ft₁)
    (β : Ft ⋙ Bt ⟶ At ⋙ Ft₁) (β' : Ft' ⋙ Bt' ⟶ At' ⋙ Ft'₁)
    (σL : Lt ⋙ Bt ⟶ Bt' ⋙ L₁t) (σK : Kt ⋙ At ⟶ At' ⋙ K₁t)
    (SL : LD ⋙ BD ⟶ BD' ⋙ L₁D) (SK : KD ⋙ AD ⟶ AD' ⋙ K₁D)
    (hSL : ∀ X, SL.app (Q₃.obj X) = BD.map (φL.hom.app X) ≫ φB.hom.app (Lt.obj X) ≫
      Q₈.map (σL.app X) ≫ φL₁.inv.app (Bt'.obj X) ≫ L₁D.map (φB'.inv.app X))
    (hSK : ∀ X, SK.app (Q₁.obj X) = AD.map (φK.hom.app X) ≫ φA.hom.app (Kt.obj X) ≫
      Q₆.map (σK.app X) ≫ φK₁.inv.app (At'.obj X) ≫ K₁D.map (φA'.inv.app X))
    (hcube : ∀ X, Bt.map (e.app X) ≫ β.app (Kt.obj X) ≫ Ft₁.map (σK.app X) =
      σL.app (Ft'.obj X) ≫ L₁t.map (β'.app X) ≫ e₁.app (At'.obj X))
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit αF' LD) W₁]
    [(RF ⋙ BD).IsRightDerivedFunctor (whiskerUnit αF BD) W₂]
    [(RF' ⋙ BD').IsRightDerivedFunctor (whiskerUnit αF' BD') W₁]
    [(RF'₁ ⋙ L₁D).IsRightDerivedFunctor (whiskerUnit αF'₁ L₁D) W₅]
    [(RF' ⋙ LD ⋙ BD).IsRightDerivedFunctor (whiskerUnit αF' (LD ⋙ BD)) W₁] (K : D₁) :
    BD.map ((squareMapOfHom W₁ φK φL αF' αF e).app K) ≫
        (squareMapOfHom W₂ φA φB αF αF₁ β).app (KD.obj K) ≫ RF₁.map (SK.app K) =
      SL.app (RF'.obj K) ≫ L₁D.map ((squareMapOfHom W₁ φA' φB' αF' αF'₁ β').app K) ≫
        (squareMapOfHom W₅ φK₁ φL₁ αF'₁ αF₁ e₁).app (AD'.obj K) := by
  let γ₁ : RF' ⋙ LD ⋙ BD ⟶ AD' ⋙ K₁D ⋙ RF₁ :=
    (Functor.associator RF' LD BD).inv ≫
      Functor.whiskerRight (squareMapOfHom W₁ φK φL αF' αF e) BD ≫
      (Functor.associator KD RF BD).hom ≫
      Functor.whiskerLeft KD (squareMapOfHom W₂ φA φB αF αF₁ β) ≫
      (Functor.associator KD AD RF₁).inv ≫ Functor.whiskerRight SK RF₁ ≫
      (Functor.associator AD' K₁D RF₁).hom
  let γ₂ : RF' ⋙ LD ⋙ BD ⟶ AD' ⋙ K₁D ⋙ RF₁ :=
    Functor.whiskerLeft RF' SL ≫ (Functor.associator RF' BD' L₁D).inv ≫
      Functor.whiskerRight (squareMapOfHom W₁ φA' φB' αF' αF'₁ β') L₁D ≫
      (Functor.associator AD' RF'₁ L₁D).hom ≫
      Functor.whiskerLeft AD' (squareMapOfHom W₅ φK₁ φL₁ αF'₁ αF₁ e₁)
  have key : γ₁ = γ₂ := by
    apply (RF' ⋙ LD ⋙ BD).rightDerived_ext (whiskerUnit αF' (LD ⋙ BD)) W₁
    ext X
    simp only [γ₁, γ₂, whiskerUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.comp_id, Category.id_comp, Functor.comp_map]
    -- the left-hand side
    have hβ := (squareMapOfHom W₂ φA φB αF αF₁ β).naturality (φK.inv.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hβ
    have hα₁ := αF₁.naturality (σK.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hα₁
    have hφB := φB.hom.naturality (e.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hφB
    have hL : BD.map (LD.map (αF'.app X)) ≫
        BD.map ((squareMapOfHom W₁ φK φL αF' αF e).app (Q₁.obj X)) ≫
        (squareMapOfHom W₂ φA φB αF αF₁ β).app (KD.obj (Q₁.obj X)) ≫
        RF₁.map (SK.app (Q₁.obj X)) =
        BD.map (φL.hom.app (Ft'.obj X)) ≫ φB.hom.app (Lt.obj (Ft'.obj X)) ≫
          Q₈.map (Bt.map (e.app X) ≫ β.app (Kt.obj X) ≫ Ft₁.map (σK.app X)) ≫
          αF₁.app (K₁t.obj (At'.obj X)) ≫ RF₁.map (φK₁.inv.app (At'.obj X)) ≫
          RF₁.map (K₁D.map (φA'.inv.app X)) := by
      have hS : RF₁.map (φA.inv.app (Kt.obj X)) ≫ RF₁.map (AD.map (φK.inv.app X)) ≫
          RF₁.map (SK.app (Q₁.obj X)) = RF₁.map (Q₆.map (σK.app X)) ≫
          RF₁.map (φK₁.inv.app (At'.obj X)) ≫ RF₁.map (K₁D.map (φA'.inv.app X)) := by
        rw [hSK X]
        simp only [← RF₁.map_comp, Category.assoc]
        congr 1
        simp only [← AD.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, AD.map_id,
          Category.id_comp, Iso.inv_hom_id_app_assoc]
      rw [← BD.map_comp_assoc, squareMapOfHom_fac_app]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hβ, squareMapOfHom_fac_app_assoc, reassoc_of% hφB, hS,
        ← reassoc_of% hα₁]
    -- the right-hand side
    have hnat := SL.naturality (αF'.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hnat
    have he₁ := (squareMapOfHom W₅ φK₁ φL₁ αF'₁ αF₁ e₁).naturality (φA'.inv.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at he₁
    have hφL₁ := φL₁.inv.naturality (β'.app X)
    simp only [Functor.comp_map, Functor.comp_obj] at hφL₁
    have hR : BD.map (LD.map (αF'.app X)) ≫ SL.app (RF'.obj (Q₁.obj X)) ≫
        L₁D.map ((squareMapOfHom W₁ φA' φB' αF' αF'₁ β').app (Q₁.obj X)) ≫
        (squareMapOfHom W₅ φK₁ φL₁ αF'₁ αF₁ e₁).app (AD'.obj (Q₁.obj X)) =
        BD.map (φL.hom.app (Ft'.obj X)) ≫ φB.hom.app (Lt.obj (Ft'.obj X)) ≫
          Q₈.map (σL.app (Ft'.obj X) ≫ L₁t.map (β'.app X) ≫ e₁.app (At'.obj X)) ≫
          αF₁.app (K₁t.obj (At'.obj X)) ≫ RF₁.map (φK₁.inv.app (At'.obj X)) ≫
          RF₁.map (K₁D.map (φA'.inv.app X)) := by
      rw [reassoc_of% hnat, ← L₁D.map_comp_assoc, squareMapOfHom_fac_app]
      simp only [Functor.map_comp, Category.assoc]
      rw [he₁, squareMapOfHom_fac_app_assoc, hSL (Ft'.obj X)]
      simp only [Category.assoc]
      rw [← L₁D.map_comp_assoc (φB'.inv.app _), Iso.inv_hom_id_app, L₁D.map_id,
        Category.id_comp, ← reassoc_of% hφL₁, Iso.inv_hom_id_app_assoc]
    rw [hL, hR, hcube X]

  have h := NatTrans.congr_app key K
  simp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.comp_id,
    Category.id_comp] at h
  exact h

end Cube

section Transport

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {C₃ : Type*} [Category* C₃]
  {C₄ : Type*} [Category* C₄]
  {F₀' F' : C₁ ⥤ C₃} {F₀ F : C₂ ⥤ C₄} {K₀ K K' : C₁ ⥤ C₂} {L₀ L L' : C₃ ⥤ C₄} {H₀ H : C₁ ⥤ C₄}

/-- **A transported square isomorphism, read through inclusions.** Let the isomorphism of a square
be `c₁ ≪≫ c₂.symm` for comparisons `c₁ : F₀' ⋙ L₀ ≅ H₀` and `c₂ : K₀ ⋙ F₀ ≅ H₀` with a common
diagonal, and suppose that, along transformations `jK : K₀ ⟶ K'`, `jL : L₀ ⟶ L'`, `jH : H₀ ⟶ H`,
the comparisons `c₁`, `c₂` correspond to comparisons `d₁ : F' ⋙ L' ≅ H` and `d₂ : K' ⋙ F ≅ H`
(the hypotheses `h₁`, `h₂`). Then the transported isomorphism of the square, followed by `jK`,
is `jL` followed by `d₁ ≪≫ d₂.symm`. -/
lemma squareIsoTransport_hom_app_comp (iF' : F₀' ≅ F') (iF : F₀ ≅ F) (iK : K ≅ K₀)
    (iL : L ≅ L₀) (c₁ : F₀' ⋙ L₀ ≅ H₀) (c₂ : K₀ ⋙ F₀ ≅ H₀) (jK : K₀ ⟶ K') (jL : L₀ ⟶ L')
    (jH : H₀ ⟶ H) (d₁ : F' ⋙ L' ≅ H) (d₂ : K' ⋙ F ≅ H)
    (h₁ : ∀ A, c₁.hom.app A ≫ jH.app A =
      jL.app (F₀'.obj A) ≫ L'.map (iF'.hom.app A) ≫ d₁.hom.app A)
    (h₂ : ∀ A, c₂.hom.app A ≫ jH.app A =
      iF.hom.app (K₀.obj A) ≫ F.map (jK.app A) ≫ d₂.hom.app A) (A : C₁) :
    (squareIsoTransport iF' iF iK iL (c₁ ≪≫ c₂.symm)).hom.app A ≫ F.map ((iK.hom ≫ jK).app A) =
      (iL.hom ≫ jL).app (F'.obj A) ≫ (d₁ ≪≫ d₂.symm).hom.app A := by
  have h₂' : c₂.inv.app A ≫ iF.hom.app (K₀.obj A) ≫ F.map (jK.app A) =
      jH.app A ≫ d₂.inv.app A := by
    rw [← cancel_epi (c₂.hom.app A), Iso.hom_inv_id_app_assoc, ← Category.assoc (c₂.hom.app A),
      h₂ A]
    simp
  have hn := jL.naturality (iF'.inv.app A)
  simp only [squareIsoTransport_hom_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Functor.map_comp, ← F.map_comp_assoc (iK.inv.app A), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h₂', reassoc_of% (h₁ A), reassoc_of% hn, ← L'.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Transport

section Restriction

variable {S₁ : Type*} [Category* S₁] {S₂ : Type*} [Category* S₂] {S₃ : Type*} [Category* S₃]
  {S₄ : Type*} [Category* S₄] {S₅ : Type*} [Category* S₅] {S₆ : Type*} [Category* S₆]
  {S₇ : Type*} [Category* S₇] {S₈ : Type*} [Category* S₈]
  {F' : S₁ ⥤ S₃} {F : S₂ ⥤ S₄} {F'₁ : S₅ ⥤ S₇} {F₁ : S₆ ⥤ S₈}
  {K Ks : S₁ ⥤ S₂} {L Ls : S₃ ⥤ S₄} {K₁ K₁s : S₅ ⥤ S₆} {L₁ L₁s : S₇ ⥤ S₈}
  {A' : S₁ ⥤ S₅} {A : S₂ ⥤ S₆} {B' : S₃ ⥤ S₇} {Bb : S₄ ⥤ S₈}

/-- **An underived cube commutes as soon as it does after including subfunctors.** Consider a
cube of functors whose top and bottom faces carry transformations `e : F' ⋙ L ⟶ K ⋙ F` and
`e₁ : F'₁ ⋙ L₁ ⟶ K₁ ⋙ F₁`, the faces along `F` and `F'` transformations `β`, `β'`, and the other
two faces transformations `σK`, `σL`; suppose that `K`, `L`, `K₁`, `L₁` map to functors `Ks`,
`Ls`, `K₁s`, `L₁s` by `jK`, `jL`, `jK₁`, `jL₁`, under which `e`, `e₁` become `P`, `P₁`
(`hE`, `hE₁`) and `σK`, `σL` become `γK`, `γL` (`hσK`, `hσL`). If the cube of `P, P₁, β, β',
γK, γL` commutes (`hcube`) and `F₁` of `jK₁` is a monomorphism, then the cube of
`e, e₁, β, β', σK, σL` commutes. In the situation of [Stacks, Tag 0F7F], `K`, `L`, `K₁`, `L₁`
are lower shrieks and `Ks`, `Ls`, `K₁s`, `L₁s` the direct images containing them. -/
theorem cube_comm_of_mono (e : F' ⋙ L ⟶ K ⋙ F) (e₁ : F'₁ ⋙ L₁ ⟶ K₁ ⋙ F₁)
    (P : F' ⋙ Ls ⟶ Ks ⋙ F) (P₁ : F'₁ ⋙ L₁s ⟶ K₁s ⋙ F₁)
    (β : F ⋙ Bb ⟶ A ⋙ F₁) (β' : F' ⋙ B' ⟶ A' ⋙ F'₁)
    (σK : K ⋙ A ⟶ A' ⋙ K₁) (σL : L ⋙ Bb ⟶ B' ⋙ L₁)
    (γK : Ks ⋙ A ⟶ A' ⋙ K₁s) (γL : Ls ⋙ Bb ⟶ B' ⋙ L₁s)
    (jK : K ⟶ Ks) (jL : L ⟶ Ls) (jK₁ : K₁ ⟶ K₁s) (jL₁ : L₁ ⟶ L₁s)
    (hE : ∀ G, e.app G ≫ F.map (jK.app G) = jL.app (F'.obj G) ≫ P.app G)
    (hE₁ : ∀ G, e₁.app G ≫ F₁.map (jK₁.app G) = jL₁.app (F'₁.obj G) ≫ P₁.app G)
    (hσK : ∀ G, σK.app G ≫ jK₁.app (A'.obj G) = A.map (jK.app G) ≫ γK.app G)
    (hσL : ∀ G, σL.app G ≫ jL₁.app (B'.obj G) = Bb.map (jL.app G) ≫ γL.app G)
    (hcube : ∀ G, Bb.map (P.app G) ≫ β.app (Ks.obj G) ≫ F₁.map (γK.app G) =
      γL.app (F'.obj G) ≫ L₁s.map (β'.app G) ≫ P₁.app (A'.obj G))
    (G : S₁) [Mono (F₁.map (jK₁.app (A'.obj G)))] :
    Bb.map (e.app G) ≫ β.app (K.obj G) ≫ F₁.map (σK.app G) =
      σL.app (F'.obj G) ≫ L₁.map (β'.app G) ≫ e₁.app (A'.obj G) := by
  rw [← cancel_mono (F₁.map (jK₁.app (A'.obj G)))]
  have hβ := β.naturality (jK.app G)
  have hj := jL₁.naturality (β'.app G)
  simp only [Functor.comp_map, Functor.comp_obj] at hβ hj
  simp only [Category.assoc, ← F₁.map_comp, hσK, hE₁]
  rw [F₁.map_comp, ← reassoc_of% hβ, ← Bb.map_comp_assoc, hE, Bb.map_comp, Category.assoc,
    hcube, reassoc_of% hj, ← reassoc_of% (hσL (F'.obj G))]

end Restriction

section Faithful

variable {𝓜₁ : Type*} [Category* 𝓜₁] {𝓜₂ : Type*} [Category* 𝓜₂] {𝓜₃ : Type*} [Category* 𝓜₃]
  {𝓜₄ : Type*} [Category* 𝓜₄] {𝓜₅ : Type*} [Category* 𝓜₅] {𝓜₆ : Type*} [Category* 𝓜₆]
  {𝓜₇ : Type*} [Category* 𝓜₇] {𝓜₈ : Type*} [Category* 𝓜₈]
  {𝓐₁ : Type*} [Category* 𝓐₁] {𝓐₂ : Type*} [Category* 𝓐₂] {𝓐₃ : Type*} [Category* 𝓐₃]
  {𝓐₄ : Type*} [Category* 𝓐₄] {𝓐₅ : Type*} [Category* 𝓐₅] {𝓐₆ : Type*} [Category* 𝓐₆]
  {𝓐₇ : Type*} [Category* 𝓐₇] {𝓐₈ : Type*} [Category* 𝓐₈]
  {φ₁ : 𝓜₁ ⥤ 𝓐₁} {φ₂ : 𝓜₂ ⥤ 𝓐₂} {φ₃ : 𝓜₃ ⥤ 𝓐₃} {φ₄ : 𝓜₄ ⥤ 𝓐₄} {φ₅ : 𝓜₅ ⥤ 𝓐₅}
  {φ₆ : 𝓜₆ ⥤ 𝓐₆} {φ₇ : 𝓜₇ ⥤ 𝓐₇} {φ₈ : 𝓜₈ ⥤ 𝓐₈}
  {F'ₘ : 𝓜₁ ⥤ 𝓜₃} {Fₘ : 𝓜₂ ⥤ 𝓜₄} {F'₁ₘ : 𝓜₅ ⥤ 𝓜₇} {F₁ₘ : 𝓜₆ ⥤ 𝓜₈}
  {Kₘ : 𝓜₁ ⥤ 𝓜₂} {Lₘ : 𝓜₃ ⥤ 𝓜₄} {K₁ₘ : 𝓜₅ ⥤ 𝓜₆} {L₁ₘ : 𝓜₇ ⥤ 𝓜₈}
  {A'ₘ : 𝓜₁ ⥤ 𝓜₅} {Aₘ : 𝓜₂ ⥤ 𝓜₆} {B'ₘ : 𝓜₃ ⥤ 𝓜₇} {Bₘ : 𝓜₄ ⥤ 𝓜₈}
  {F' : 𝓐₁ ⥤ 𝓐₃} {F : 𝓐₂ ⥤ 𝓐₄} {F'₁ : 𝓐₅ ⥤ 𝓐₇} {F₁ : 𝓐₆ ⥤ 𝓐₈}
  {K : 𝓐₁ ⥤ 𝓐₂} {L : 𝓐₃ ⥤ 𝓐₄} {K₁ : 𝓐₅ ⥤ 𝓐₆} {L₁ : 𝓐₇ ⥤ 𝓐₈}
  {A' : 𝓐₁ ⥤ 𝓐₅} {A : 𝓐₂ ⥤ 𝓐₆} {B' : 𝓐₃ ⥤ 𝓐₇} {Bb : 𝓐₄ ⥤ 𝓐₈}

/-- **A commuting cube is reflected by faithful functors.** Suppose that functors `Xₘ` between
categories `𝓜ᵢ` lift functors `X` between categories `𝓐ᵢ` along `φᵢ : 𝓜ᵢ ⥤ 𝓐ᵢ`, through
isomorphisms `ηX : Xₘ ⋙ φ ≅ φ ⋙ X`, and that the transformations `eₘ, e₁ₘ, βₘ, β'ₘ, σKₘ, σLₘ` of
the faces of a cube lift transformations `e, e₁, β, β', σK, σL`, in the sense that `φ` takes their
components to those of the latter conjugated by the `η`. If `φ₈` is faithful and the cube of
`e, e₁, β, β', σK, σL` commutes, so does the cube of the lifts. -/
theorem cube_of_faithful [φ₈.Faithful]
    (ηF' : F'ₘ ⋙ φ₃ ≅ φ₁ ⋙ F') (ηF : Fₘ ⋙ φ₄ ≅ φ₂ ⋙ F) (ηF'₁ : F'₁ₘ ⋙ φ₇ ≅ φ₅ ⋙ F'₁)
    (ηF₁ : F₁ₘ ⋙ φ₈ ≅ φ₆ ⋙ F₁) (ηK : Kₘ ⋙ φ₂ ≅ φ₁ ⋙ K) (ηL : Lₘ ⋙ φ₄ ≅ φ₃ ⋙ L)
    (ηK₁ : K₁ₘ ⋙ φ₆ ≅ φ₅ ⋙ K₁) (ηL₁ : L₁ₘ ⋙ φ₈ ≅ φ₇ ⋙ L₁) (ηA' : A'ₘ ⋙ φ₅ ≅ φ₁ ⋙ A')
    (ηA : Aₘ ⋙ φ₆ ≅ φ₂ ⋙ A) (ηB' : B'ₘ ⋙ φ₇ ≅ φ₃ ⋙ B') (ηB : Bₘ ⋙ φ₈ ≅ φ₄ ⋙ Bb)
    (eₘ : F'ₘ ⋙ Lₘ ⟶ Kₘ ⋙ Fₘ) (e₁ₘ : F'₁ₘ ⋙ L₁ₘ ⟶ K₁ₘ ⋙ F₁ₘ)
    (βₘ : Fₘ ⋙ Bₘ ⟶ Aₘ ⋙ F₁ₘ) (β'ₘ : F'ₘ ⋙ B'ₘ ⟶ A'ₘ ⋙ F'₁ₘ)
    (σKₘ : Kₘ ⋙ Aₘ ⟶ A'ₘ ⋙ K₁ₘ) (σLₘ : Lₘ ⋙ Bₘ ⟶ B'ₘ ⋙ L₁ₘ)
    (e : F' ⋙ L ⟶ K ⋙ F) (e₁ : F'₁ ⋙ L₁ ⟶ K₁ ⋙ F₁)
    (β : F ⋙ Bb ⟶ A ⋙ F₁) (β' : F' ⋙ B' ⟶ A' ⋙ F'₁)
    (σK : K ⋙ A ⟶ A' ⋙ K₁) (σL : L ⋙ Bb ⟶ B' ⋙ L₁)
    (he : ∀ X, φ₄.map (eₘ.app X) = ηL.hom.app (F'ₘ.obj X) ≫ L.map (ηF'.hom.app X) ≫
      e.app (φ₁.obj X) ≫ F.map (ηK.inv.app X) ≫ ηF.inv.app (Kₘ.obj X))
    (he₁ : ∀ X, φ₈.map (e₁ₘ.app X) = ηL₁.hom.app (F'₁ₘ.obj X) ≫ L₁.map (ηF'₁.hom.app X) ≫
      e₁.app (φ₅.obj X) ≫ F₁.map (ηK₁.inv.app X) ≫ ηF₁.inv.app (K₁ₘ.obj X))
    (hβ : ∀ X, φ₈.map (βₘ.app X) = ηB.hom.app (Fₘ.obj X) ≫ Bb.map (ηF.hom.app X) ≫
      β.app (φ₂.obj X) ≫ F₁.map (ηA.inv.app X) ≫ ηF₁.inv.app (Aₘ.obj X))
    (hβ' : ∀ X, φ₇.map (β'ₘ.app X) = ηB'.hom.app (F'ₘ.obj X) ≫ B'.map (ηF'.hom.app X) ≫
      β'.app (φ₁.obj X) ≫ F'₁.map (ηA'.inv.app X) ≫ ηF'₁.inv.app (A'ₘ.obj X))
    (hσK : ∀ X, φ₆.map (σKₘ.app X) = ηA.hom.app (Kₘ.obj X) ≫ A.map (ηK.hom.app X) ≫
      σK.app (φ₁.obj X) ≫ K₁.map (ηA'.inv.app X) ≫ ηK₁.inv.app (A'ₘ.obj X))
    (hσL : ∀ X, φ₈.map (σLₘ.app X) = ηB.hom.app (Lₘ.obj X) ≫ Bb.map (ηL.hom.app X) ≫
      σL.app (φ₃.obj X) ≫ L₁.map (ηB'.inv.app X) ≫ ηL₁.inv.app (B'ₘ.obj X))
    (hcube : ∀ G, Bb.map (e.app G) ≫ β.app (K.obj G) ≫ F₁.map (σK.app G) =
      σL.app (F'.obj G) ≫ L₁.map (β'.app G) ≫ e₁.app (A'.obj G)) (X : 𝓜₁) :
    Bₘ.map (eₘ.app X) ≫ βₘ.app (Kₘ.obj X) ≫ F₁ₘ.map (σKₘ.app X) =
      σLₘ.app (F'ₘ.obj X) ≫ L₁ₘ.map (β'ₘ.app X) ≫ e₁ₘ.app (A'ₘ.obj X) := by
  apply φ₈.map_injective
  have mB := (NatIso.naturality_2 ηB (eₘ.app X)).symm
  have mF₁ := (NatIso.naturality_2 ηF₁ (σKₘ.app X)).symm
  have mL₁ := (NatIso.naturality_2 ηL₁ (β'ₘ.app X)).symm
  simp only [Functor.comp_map] at mB mF₁ mL₁
  have nβ := β.naturality (ηK.inv.app X)
  have nσL := σL.naturality (ηF'.hom.app X)
  have ne₁ := e₁.naturality (ηA'.inv.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at nβ nσL ne₁
  have c₁ : Bb.map (ηF.inv.app (Kₘ.obj X)) ≫ Bb.map (ηF.hom.app (Kₘ.obj X)) = 𝟙 _ := by
    rw [← Bb.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have c₂ : F₁.map (ηA.inv.app (Kₘ.obj X)) ≫ F₁.map (ηA.hom.app (Kₘ.obj X)) = 𝟙 _ := by
    rw [← F₁.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have c₃ : F₁.map (A.map (ηK.inv.app X)) ≫ F₁.map (A.map (ηK.hom.app X)) = 𝟙 _ := by
    rw [← F₁.map_comp, ← A.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  have c₄ : L₁.map (ηB'.inv.app (F'ₘ.obj X)) ≫ L₁.map (ηB'.hom.app (F'ₘ.obj X)) = 𝟙 _ := by
    rw [← L₁.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have c₅ : L₁.map (ηF'₁.inv.app (A'ₘ.obj X)) ≫ L₁.map (ηF'₁.hom.app (A'ₘ.obj X)) = 𝟙 _ := by
    rw [← L₁.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hL : φ₈.map (Bₘ.map (eₘ.app X) ≫ βₘ.app (Kₘ.obj X) ≫ F₁ₘ.map (σKₘ.app X)) =
      ηB.hom.app _ ≫ Bb.map (ηL.hom.app (F'ₘ.obj X)) ≫ Bb.map (L.map (ηF'.hom.app X)) ≫
        (Bb.map (e.app (φ₁.obj X)) ≫ β.app (K.obj (φ₁.obj X)) ≫ F₁.map (σK.app (φ₁.obj X))) ≫
        F₁.map (K₁.map (ηA'.inv.app X)) ≫ F₁.map (ηK₁.inv.app (A'ₘ.obj X)) ≫
        ηF₁.inv.app _ := by
    rw [Functor.map_comp, Functor.map_comp, mB, mF₁, he, hβ, hσK]
    simp only [Functor.comp_obj, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
      reassoc_of% c₁, reassoc_of% c₂]
    rw [reassoc_of% nβ, reassoc_of% c₃]
  have hR : φ₈.map (σLₘ.app (F'ₘ.obj X) ≫ L₁ₘ.map (β'ₘ.app X) ≫ e₁ₘ.app (A'ₘ.obj X)) =
      ηB.hom.app _ ≫ Bb.map (ηL.hom.app (F'ₘ.obj X)) ≫ Bb.map (L.map (ηF'.hom.app X)) ≫
        (σL.app (F'.obj (φ₁.obj X)) ≫ L₁.map (β'.app (φ₁.obj X)) ≫
          e₁.app (A'.obj (φ₁.obj X))) ≫
        F₁.map (K₁.map (ηA'.inv.app X)) ≫ F₁.map (ηK₁.inv.app (A'ₘ.obj X)) ≫
        ηF₁.inv.app _ := by
    rw [Functor.map_comp, Functor.map_comp, mL₁, hσL, hβ', he₁]
    simp only [Functor.comp_obj, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
      reassoc_of% c₄, reassoc_of% c₅]
    rw [reassoc_of% nσL, reassoc_of% ne₁]
  rw [hL, hR, hcube]

end Faithful

section HomotopyCategory

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] {C₂ : Type*} [Category* C₂] [Preadditive C₂]
  {C₃ : Type*} [Category* C₃] [Preadditive C₃] {C₄ : Type*} [Category* C₄] [Preadditive C₄]
  {ι : Type*} (c : ComplexShape ι)
  {F' : C₁ ⥤ C₃} {F : C₂ ⥤ C₄} {K : C₁ ⥤ C₂} {L : C₃ ⥤ C₄}
  [F'.Additive] [F.Additive] [K.Additive] [L.Additive]

/-- A transformation of a square of additive functors, induced on homotopy categories. -/
def homotopySquareHom (e : F' ⋙ L ⟶ K ⋙ F) :
    F'.mapHomotopyCategory c ⋙ L.mapHomotopyCategory c ⟶
      K.mapHomotopyCategory c ⋙ F.mapHomotopyCategory c :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl (F' ⋙ L)) c).hom ≫
    NatTrans.mapHomotopyCategory e c ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (K ⋙ F)) c).inv

/-- The component of `homotopySquareHom c e` at `X` is the image in the homotopy category of the
component of `e` on homological complexes at `X.as`. -/
lemma homotopySquareHom_app (e : F' ⋙ L ⟶ K ⋙ F) (X : HomotopyCategory C₁ c) :
    (homotopySquareHom c e).app X =
      (HomotopyCategory.quotient C₄ c).map ((NatTrans.mapHomologicalComplex e c).app X.as) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have h₂ : (Functor.mapHomotopyCategoryCompIso (Iso.refl (K ⋙ F)) c).inv.app
      ((HomotopyCategory.quotient C₁ c).obj X) = (HomotopyCategory.quotient C₄ c).map
        ((NatTrans.mapHomologicalComplex (Iso.refl (K ⋙ F)).inv c).app X) := rfl
  simp only [homotopySquareHom, NatTrans.comp_app,
    CategoryTheory.mapHomotopyCategoryCompIso_hom_app, h₂, Iso.refl_hom, Iso.refl_inv,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, NatTrans.mapHomotopyCategory_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The transformation induced on homotopy categories by an isomorphism of a square is the
isomorphism `homotopySquareIso`. -/
lemma homotopySquareHom_hom (e : F' ⋙ L ≅ K ⋙ F) :
    homotopySquareHom c e.hom = (homotopySquareIso c e).hom := by
  ext X
  rw [homotopySquareHom_app, homotopySquareIso_hom_app]

end HomotopyCategory

section HomotopyCube

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] {C₂ : Type*} [Category* C₂] [Preadditive C₂]
  {C₃ : Type*} [Category* C₃] [Preadditive C₃] {C₄ : Type*} [Category* C₄] [Preadditive C₄]
  {C₅ : Type*} [Category* C₅] [Preadditive C₅] {C₆ : Type*} [Category* C₆] [Preadditive C₆]
  {C₇ : Type*} [Category* C₇] [Preadditive C₇] {C₈ : Type*} [Category* C₈] [Preadditive C₈]
  {ι : Type*} (c : ComplexShape ι)
  {F' : C₁ ⥤ C₃} {F : C₂ ⥤ C₄} {F'₁ : C₅ ⥤ C₇} {F₁ : C₆ ⥤ C₈}
  {K : C₁ ⥤ C₂} {L : C₃ ⥤ C₄} {K₁ : C₅ ⥤ C₆} {L₁ : C₇ ⥤ C₈}
  {A' : C₁ ⥤ C₅} {A : C₂ ⥤ C₆} {B' : C₃ ⥤ C₇} {Bb : C₄ ⥤ C₈}
  [F'.Additive] [F.Additive] [F'₁.Additive] [F₁.Additive] [K.Additive] [L.Additive]
  [K₁.Additive] [L₁.Additive] [A'.Additive] [A.Additive] [B'.Additive] [Bb.Additive]

/-- **A commuting cube of additive functors induces one on homotopy categories.** -/
lemma homotopySquareHom_cube (e : F' ⋙ L ⟶ K ⋙ F) (e₁ : F'₁ ⋙ L₁ ⟶ K₁ ⋙ F₁)
    (β : F ⋙ Bb ⟶ A ⋙ F₁) (β' : F' ⋙ B' ⟶ A' ⋙ F'₁)
    (σK : K ⋙ A ⟶ A' ⋙ K₁) (σL : L ⋙ Bb ⟶ B' ⋙ L₁)
    (h : ∀ G, Bb.map (e.app G) ≫ β.app (K.obj G) ≫ F₁.map (σK.app G) =
      σL.app (F'.obj G) ≫ L₁.map (β'.app G) ≫ e₁.app (A'.obj G))
    (X : HomotopyCategory C₁ c) :
    (Bb.mapHomotopyCategory c).map ((homotopySquareHom c e).app X) ≫
        (homotopySquareHom c β).app ((K.mapHomotopyCategory c).obj X) ≫
        (F₁.mapHomotopyCategory c).map ((homotopySquareHom c σK).app X) =
      (homotopySquareHom c σL).app ((F'.mapHomotopyCategory c).obj X) ≫
        (L₁.mapHomotopyCategory c).map ((homotopySquareHom c β').app X) ≫
        (homotopySquareHom c e₁).app ((A'.mapHomotopyCategory c).obj X) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [homotopySquareHom_app, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as]
  change (HomotopyCategory.quotient C₈ c).map ((Bb.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex e c).app X)) ≫
      (HomotopyCategory.quotient C₈ c).map
        ((NatTrans.mapHomologicalComplex β c).app ((K.mapHomologicalComplex c).obj X)) ≫
      (HomotopyCategory.quotient C₈ c).map ((F₁.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex σK c).app X)) =
    (HomotopyCategory.quotient C₈ c).map
        ((NatTrans.mapHomologicalComplex σL c).app ((F'.mapHomologicalComplex c).obj X)) ≫
      (HomotopyCategory.quotient C₈ c).map ((L₁.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex β' c).app X)) ≫
      (HomotopyCategory.quotient C₈ c).map
        ((NatTrans.mapHomologicalComplex e₁ c).app ((A'.mapHomologicalComplex c).obj X))
  simp only [← Functor.map_comp]
  congr 1
  ext n
  simpa using h (X.X n)

end HomotopyCube

end Stacks.DerivedBaseChange

end
