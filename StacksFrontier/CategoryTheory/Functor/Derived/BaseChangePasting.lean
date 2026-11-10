module

public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedComp
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition

/-!
# Base change maps of right derived functors along exact functors, and their pasting

Consider a square of functors
```
K₁ --Kt--> K₂
|          |
Ft'        Ft
v          v
K₃ --Lt--> K₄
```
together with localization functors `Qᵢ : Kᵢ ⥤ Dᵢ`, functors `KD : D₁ ⥤ D₂`, `LD : D₃ ⥤ D₄`
induced by `Kt` and `Lt` (that is, with isomorphisms `Q₁ ⋙ KD ≅ Kt ⋙ Q₂` and
`Q₃ ⋙ LD ≅ Lt ⋙ Q₄`), right derived functors `RF'` of `Ft'` and `RF` of `Ft`, and an isomorphism
`e : Ft' ⋙ Lt ≅ Kt ⋙ Ft`. If `RF' ⋙ LD` is again a right derived functor of `Ft' ⋙ Q₃ ⋙ LD`, its
universal property produces a canonical *base change map*
```
LD ∘ RF' ⟶ RF ∘ KD,
```
the unique transformation which, precomposed with the unit of `RF'`, is the composite
`LD (Ft' X) ≅ Lt Ft' X ≅ Ft Kt X ⟶ RF (Kt X) ≅ RF (KD X)` assembled from `e` and the unit of `RF`.

In the situation of the source, `Kt` and `Lt` are the functors induced on homotopy categories by
exact functors `k_!` and `l_!`, `Ft'` and `Ft` the functors induced by direct images `f'_*` and
`f_*`, and the base change map is the map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` of [Stacks, Tag 0F7B].

The main result is the compatibility of these maps with vertical pasting of squares: for two
squares on top of each other, with outer vertical functors `Pt' ≅ Ft' ⋙ Gt'` and `Pt ≅ Ft ⋙ Gt`,
the base change map of the outer rectangle, followed by the canonical comparison
`RP ⟶ RG ∘ RF` of [Stacks, Tag 05T2], is the composite of the two base change maps, preceded by
the comparison `RP' ⟶ RG' ∘ RF'`. The only input is that the isomorphisms `e` of the three
squares paste.

Three auxiliary pieces produce that input in practice. `squareIsoTransport` transports the
isomorphism of a square along isomorphisms of its four sides, and
`squareIsoTransport_vertical_paste` says that pasting survives the transport.
`vertical_paste_of_faithful` says that pasting of lifted
isomorphisms along faithful functors follows from pasting downstairs. `homotopySquareIso` is the
isomorphism of a square of additive functors induced on homotopy categories, and
`homotopySquareIso_vertical_paste` says that pasting is inherited.

## Main definitions

* `Stacks.DerivedBaseChange.squareMap`: the base change map of a square.
* `Stacks.DerivedBaseChange.compComparison`: the comparison `RP ⟶ RF ⋙ RG` of a right derived
  functor of `Pt ≅ Ft ⋙ Gt` with the composite of right derived functors of `Ft` and `Gt`.
* `Stacks.DerivedBaseChange.squareIsoTransport`: transport of a square isomorphism along
  isomorphisms of the sides.
* `Stacks.DerivedBaseChange.homotopySquareIso`: a square isomorphism of additive functors, on
  homotopy categories.

## Main results

* `Stacks.DerivedBaseChange.squareMap_fac_app`: the characterizing property of the base change
  map.
* `Stacks.DerivedBaseChange.squareMap_vertical_paste`: the compatibility with vertical pasting.
* `Stacks.DerivedBaseChange.squareIsoTransport_vertical_paste`,
  `Stacks.DerivedBaseChange.vertical_paste_of_faithful` and
  `Stacks.DerivedBaseChange.homotopySquareIso_vertical_paste`: pasting of the underived
  isomorphisms is preserved by transport, reflected by faithful functors, and inherited on
  homotopy categories.
* `Stacks.DerivedBaseChange.isRightDerivedFunctor_comp_right`: over a Grothendieck abelian
  category, a right derived functor on the unbounded derived category followed by an arbitrary
  functor is a right derived functor of the composite. This is what makes the base change map
  defined in the source's situation.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7C](https://stacks.math.columbia.edu/tag/0F7C)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedBaseChange

section Square

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄}
  {Kt : K₁ ⥤ K₂} {KD : D₁ ⥤ D₂} {Lt : K₃ ⥤ K₄} {LD : D₃ ⥤ D₄}
  {Ft' : K₁ ⥤ K₃} {RF' : D₁ ⥤ D₃} {Ft : K₂ ⥤ K₄} {RF : D₂ ⥤ D₄}

/-- The transformation out of `Ft' ⋙ Q₃ ⋙ LD` which the base change map of a square extends:
`LD (Ft' X) ≅ Lt (Ft' X) ≅ Ft (Kt X) ⟶ RF (Kt X) ≅ RF (KD X)`. -/
def squareMapUnit (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ≅ Kt ⋙ Ft) :
    (Ft' ⋙ Q₃) ⋙ LD ⟶ Q₁ ⋙ KD ⋙ RF :=
  (Functor.associator Ft' Q₃ LD).hom ≫ Functor.whiskerLeft Ft' φL.hom ≫
    (Functor.associator Ft' Lt Q₄).inv ≫ Functor.whiskerRight e.hom Q₄ ≫
    (Functor.associator Kt Ft Q₄).hom ≫ Functor.whiskerLeft Kt α ≫
    (Functor.associator Kt Q₂ RF).inv ≫ Functor.whiskerRight φK.inv RF ≫
    (Functor.associator Q₁ KD RF).hom

/-- The component of `squareMapUnit φK φL α e` at `X` is the composite
`φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.hom.app X) ≫ α.app (Kt.obj X) ≫ RF.map (φK.inv.app X)`. -/
@[simp]
lemma squareMapUnit_app (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ≅ Kt ⋙ Ft) (X : K₁) :
    (squareMapUnit φK φL α e).app X =
      φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.hom.app X) ≫ α.app (Kt.obj X) ≫
        RF.map (φK.inv.app X) := by
  simp [squareMapUnit]

/-- The unit of `RF'` followed by `LD`, exhibiting `RF' ⋙ LD` as a candidate right derived
functor of `Ft' ⋙ Q₃ ⋙ LD`. -/
abbrev whiskerUnit {F : K₁ ⥤ D₃} (α' : F ⟶ Q₁ ⋙ RF') (LD : D₃ ⥤ D₄) :
    F ⋙ LD ⟶ Q₁ ⋙ RF' ⋙ LD :=
  Functor.whiskerRight α' LD ≫ (Functor.associator Q₁ RF' LD).hom

variable (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]

/-- **The base change map of a square.** For a square of functors `Ft' ⋙ Lt ≅ Kt ⋙ Ft` between
categories with localizations, with `KD` and `LD` induced by `Kt` and `Lt`, and right derived
functors `RF'` of `Ft'` and `RF` of `Ft`, this is the transformation `LD ∘ RF' ⟶ RF ∘ KD`
characterized by `squareMap_fac_app`. In the source's situation it is the map of
[Stacks, Tag 0F7B]. -/
def squareMap (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ≅ Kt ⋙ Ft)
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit α' LD) W₁] :
    RF' ⋙ LD ⟶ KD ⋙ RF :=
  (RF' ⋙ LD).rightDerivedDesc (whiskerUnit α' LD) W₁ (KD ⋙ RF) (squareMapUnit φK φL α e)

/-- The base change map of a square, precomposed with the unit of `RF'`, is the composite
`LD (Ft' X) ≅ Lt (Ft' X) ≅ Ft (Kt X) ⟶ RF (Kt X) ≅ RF (KD X)`. -/
@[reassoc]
lemma squareMap_fac_app (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄)
    (α' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (α : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF) (e : Ft' ⋙ Lt ≅ Kt ⋙ Ft)
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit α' LD) W₁] (X : K₁) :
    LD.map (α'.app X) ≫ (squareMap W₁ φK φL α' α e).app (Q₁.obj X) =
      φL.hom.app (Ft'.obj X) ≫ Q₄.map (e.hom.app X) ≫ α.app (Kt.obj X) ≫
        RF.map (φK.inv.app X) := by
  have h := (RF' ⋙ LD).rightDerived_fac_app (whiskerUnit α' LD) W₁ (KD ⋙ RF)
    (squareMapUnit φK φL α e) X
  simp only [whiskerUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id, squareMapUnit_app] at h
  exact h

end Square

section Comparison

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃}
  {Ft : K₁ ⥤ K₂} {RF : D₁ ⥤ D₂} {Gt : K₂ ⥤ K₃} {RG : D₂ ⥤ D₃} {Pt : K₁ ⥤ K₃} {RP : D₁ ⥤ D₃}
  (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]

/-- **The comparison of a right derived functor of a composite with the composite of the right
derived functors** ([Stacks, Tag 05T2]): for `d : Ft ⋙ Gt ≅ Pt`, the unique transformation
`RP ⟶ RF ⋙ RG` which, precomposed with the unit of `RP`, is
`Pt X ≅ Gt (Ft X) ⟶ RG (Ft X) ⟶ RG (RF X)`. -/
def compComparison (αF : Ft ⋙ Q₂ ⟶ Q₁ ⋙ RF) (αG : Gt ⋙ Q₃ ⟶ Q₂ ⋙ RG)
    (αP : Pt ⋙ Q₃ ⟶ Q₁ ⋙ RP) (d : Ft ⋙ Gt ≅ Pt) [RP.IsRightDerivedFunctor αP W₁] :
    RP ⟶ RF ⋙ RG :=
  RP.rightDerivedDesc αP W₁ (RF ⋙ RG)
    (Functor.whiskerRight d.inv Q₃ ≫ Functor.rightDerivedCompUnit αF αG)

/-- The comparison `RP ⟶ RF ⋙ RG`, precomposed with the unit of `RP`, is
`Pt X ≅ Gt (Ft X) ⟶ RG (Ft X) ⟶ RG (RF X)`. -/
@[reassoc]
lemma compComparison_fac_app (αF : Ft ⋙ Q₂ ⟶ Q₁ ⋙ RF) (αG : Gt ⋙ Q₃ ⟶ Q₂ ⋙ RG)
    (αP : Pt ⋙ Q₃ ⟶ Q₁ ⋙ RP) (d : Ft ⋙ Gt ≅ Pt) [RP.IsRightDerivedFunctor αP W₁] (X : K₁) :
    αP.app X ≫ (compComparison W₁ αF αG αP d).app (Q₁.obj X) =
      Q₃.map (d.inv.app X) ≫ αG.app (Ft.obj X) ≫ RG.map (αF.app X) := by
  have h := RP.rightDerived_fac_app αP W₁ (RF ⋙ RG)
    (Functor.whiskerRight d.inv Q₃ ≫ Functor.rightDerivedCompUnit αF αG) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.rightDerivedCompUnit_app] at h
  exact h

end Comparison

section Paste

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {K₅ : Type*} [Category* K₅] {K₆ : Type*} [Category* K₆]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {D₅ : Type*} [Category* D₅] {D₆ : Type*} [Category* D₆]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄} {Q₅ : K₅ ⥤ D₅} {Q₆ : K₆ ⥤ D₆}
  {Kt : K₁ ⥤ K₂} {KD : D₁ ⥤ D₂} {Lt : K₃ ⥤ K₄} {LD : D₃ ⥤ D₄} {Mt : K₅ ⥤ K₆} {MD : D₅ ⥤ D₆}
  {Ft' : K₁ ⥤ K₃} {RF' : D₁ ⥤ D₃} {Ft : K₂ ⥤ K₄} {RF : D₂ ⥤ D₄}
  {Gt' : K₃ ⥤ K₅} {RG' : D₃ ⥤ D₅} {Gt : K₄ ⥤ K₆} {RG : D₄ ⥤ D₆}
  {Pt' : K₁ ⥤ K₅} {RP' : D₁ ⥤ D₅} {Pt : K₂ ⥤ K₆} {RP : D₂ ⥤ D₆}
  (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]
  (W₂ : MorphismProperty K₂) [Q₂.IsLocalization W₂]
  (W₃ : MorphismProperty K₃) [Q₃.IsLocalization W₃]

/-- **Vertical pasting of base change maps.** Given two squares `e₁ : Ft' ⋙ Lt ≅ Kt ⋙ Ft` and
`e₂ : Gt' ⋙ Mt ≅ Lt ⋙ Gt` on top of each other, outer vertical functors `d' : Ft' ⋙ Gt' ≅ Pt'` and
`d : Ft ⋙ Gt ≅ Pt`, and an isomorphism `e : Pt' ⋙ Mt ≅ Kt ⋙ Pt` for the outer rectangle which is
the pasting of `e₁` and `e₂` (the hypothesis `hpaste`), the base change map of the rectangle
followed by the comparison `RP ⟶ RF ⋙ RG` is the comparison `RP' ⟶ RF' ⋙ RG'` followed by the base
change map of the lower square and then the one of the upper square. -/
theorem squareMap_vertical_paste
    (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₂) (φL : Q₃ ⋙ LD ≅ Lt ⋙ Q₄) (φM : Q₅ ⋙ MD ≅ Mt ⋙ Q₆)
    (αF' : Ft' ⋙ Q₃ ⟶ Q₁ ⋙ RF') (αF : Ft ⋙ Q₄ ⟶ Q₂ ⋙ RF)
    (αG' : Gt' ⋙ Q₅ ⟶ Q₃ ⋙ RG') (αG : Gt ⋙ Q₆ ⟶ Q₄ ⋙ RG)
    (αP' : Pt' ⋙ Q₅ ⟶ Q₁ ⋙ RP') (αP : Pt ⋙ Q₆ ⟶ Q₂ ⋙ RP)
    (d' : Ft' ⋙ Gt' ≅ Pt') (d : Ft ⋙ Gt ≅ Pt)
    (e₁ : Ft' ⋙ Lt ≅ Kt ⋙ Ft) (e₂ : Gt' ⋙ Mt ≅ Lt ⋙ Gt) (e : Pt' ⋙ Mt ≅ Kt ⋙ Pt)
    (hpaste : ∀ X : K₁, Mt.map (d'.hom.app X) ≫ e.hom.app X =
      e₂.hom.app (Ft'.obj X) ≫ Gt.map (e₁.hom.app X) ≫ d.hom.app (Kt.obj X))
    [RP'.IsRightDerivedFunctor αP' W₁] [RP.IsRightDerivedFunctor αP W₂]
    [(RF' ⋙ LD).IsRightDerivedFunctor (whiskerUnit αF' LD) W₁]
    [(RG' ⋙ MD).IsRightDerivedFunctor (whiskerUnit αG' MD) W₃]
    [(RP' ⋙ MD).IsRightDerivedFunctor (whiskerUnit αP' MD) W₁] :
    squareMap W₁ φK φM αP' αP e ≫ Functor.whiskerLeft KD (compComparison W₂ αF αG αP d) =
      Functor.whiskerRight (compComparison W₁ αF' αG' αP' d') MD ≫
        (Functor.associator RF' RG' MD).hom ≫
        Functor.whiskerLeft RF' (squareMap W₃ φL φM αG' αG e₂) ≫
        (Functor.associator RF' LD RG).inv ≫
        Functor.whiskerRight (squareMap W₁ φK φL αF' αF e₁) RG ≫
        (Functor.associator KD RF RG).hom := by
  apply (RP' ⋙ MD).rightDerived_ext (whiskerUnit αP' MD) W₁
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.comp_id,
    Category.id_comp, whiskerUnit]
  have hc := (compComparison W₂ αF αG αP d).naturality (φK.inv.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at hc
  have hτ := (squareMap W₃ φL φM αG' αG e₂).naturality (αF'.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at hτ
  rw [squareMap_fac_app_assoc, hc, compComparison_fac_app_assoc,
    ← MD.map_comp_assoc, compComparison_fac_app, MD.map_comp, MD.map_comp, Category.assoc,
    Category.assoc, reassoc_of% hτ, squareMap_fac_app_assoc,
    ← RG.map_comp (LD.map (αF'.app X)), squareMap_fac_app, ← RG.map_comp (φL.inv.app _),
    Iso.inv_hom_id_app_assoc, RG.map_comp, RG.map_comp]
  have hαG := αG.naturality (e₁.hom.app X)
  have hφM := φM.hom.naturality (d'.inv.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at hαG hφM
  have hp : e.hom.app X ≫ d.inv.app (Kt.obj X) =
      Mt.map (d'.inv.app X) ≫ e₂.hom.app (Ft'.obj X) ≫ Gt.map (e₁.hom.app X) := by
    rw [← cancel_epi (Mt.map (d'.hom.app X)), ← Category.assoc, hpaste X]
    simp
  rw [reassoc_of% hφM, ← reassoc_of% hαG, ← Q₆.map_comp_assoc, hp]
  simp

end Paste

/-- Applying a functor to `e.inv.app X` followed by `e.hom.app X` gives the identity. -/
private lemma map_inv_app_hom_app_assoc {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) {Z : E} (f : F.obj (H.obj X) ⟶ Z) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) ≫ f = f := by
  simp [← F.map_comp_assoc]

section Transport

/-! ### Transporting the isomorphism of a square along isomorphisms of its sides -/

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {C₃ : Type*} [Category* C₃]
  {C₄ : Type*} [Category* C₄] {C₅ : Type*} [Category* C₅] {C₆ : Type*} [Category* C₆]
  {F₀' F' : C₁ ⥤ C₃} {F₀ F : C₂ ⥤ C₄} {K₀ K : C₁ ⥤ C₂} {L₀ L : C₃ ⥤ C₄}

/-- An isomorphism `F₀' ⋙ L₀ ≅ K₀ ⋙ F₀` of a square, transported along isomorphisms of its four
sides to an isomorphism `F' ⋙ L ≅ K ⋙ F`. -/
def squareIsoTransport (iF' : F₀' ≅ F') (iF : F₀ ≅ F) (iK : K ≅ K₀) (iL : L ≅ L₀)
    (sq : F₀' ⋙ L₀ ≅ K₀ ⋙ F₀) : F' ⋙ L ≅ K ⋙ F :=
  Functor.isoWhiskerLeft F' iL ≪≫ Functor.isoWhiskerRight iF'.symm L₀ ≪≫ sq ≪≫
    Functor.isoWhiskerLeft K₀ iF ≪≫ Functor.isoWhiskerRight iK.symm F

/-- The component at `A` of the transported square isomorphism is the composite of the
components of `iL.hom`, `L₀.map iF'.inv`, `sq.hom`, `iF.hom` and `F.map iK.inv`. -/
@[simp]
lemma squareIsoTransport_hom_app (iF' : F₀' ≅ F') (iF : F₀ ≅ F) (iK : K ≅ K₀) (iL : L ≅ L₀)
    (sq : F₀' ⋙ L₀ ≅ K₀ ⋙ F₀) (A : C₁) :
    (squareIsoTransport iF' iF iK iL sq).hom.app A =
      iL.hom.app (F'.obj A) ≫ L₀.map (iF'.inv.app A) ≫ sq.hom.app A ≫ iF.hom.app (K₀.obj A) ≫
        F.map (iK.inv.app A) := by
  simp [squareIsoTransport]

variable {G₀' G' : C₃ ⥤ C₅} {G₀ G : C₄ ⥤ C₆} {M₀ M : C₅ ⥤ C₆}
  {P₀' P' : C₁ ⥤ C₅} {P₀ P : C₂ ⥤ C₆}

/-- **Vertical pasting of transported square isomorphisms.** Suppose the isomorphisms `sq`, `sq₂`
and `sqR` of two squares and of their outer rectangle paste (`hpaste`), with respect to
comparisons `cP' : F₀' ⋙ G₀' ≅ P₀'` and `cP : F₀ ⋙ G₀ ≅ P₀` of the outer vertical sides, and
that these comparisons correspond to comparisons `d' : F' ⋙ G' ≅ P'` and `d : F ⋙ G ≅ P` under
the isomorphisms of the vertical sides (`hc'` and `hc`). Then the transported isomorphisms paste
with respect to `d'` and `d`. -/
lemma squareIsoTransport_vertical_paste (iF' : F₀' ≅ F') (iF : F₀ ≅ F) (iK : K ≅ K₀)
    (iL : L ≅ L₀) (iG' : G₀' ≅ G') (iG : G₀ ≅ G) (iM : M ≅ M₀) (iP' : P₀' ≅ P') (iP : P₀ ≅ P)
    (sq : F₀' ⋙ L₀ ≅ K₀ ⋙ F₀) (sq₂ : G₀' ⋙ M₀ ≅ L₀ ⋙ G₀) (sqR : P₀' ⋙ M₀ ≅ K₀ ⋙ P₀)
    (cP' : F₀' ⋙ G₀' ≅ P₀') (cP : F₀ ⋙ G₀ ≅ P₀) (d' : F' ⋙ G' ≅ P') (d : F ⋙ G ≅ P)
    (hc' : ∀ A, cP'.hom.app A ≫ iP'.hom.app A =
      iG'.hom.app (F₀'.obj A) ≫ G'.map (iF'.hom.app A) ≫ d'.hom.app A)
    (hc : ∀ A, cP.hom.app A ≫ iP.hom.app A =
      iG.hom.app (F₀.obj A) ≫ G.map (iF.hom.app A) ≫ d.hom.app A)
    (hpaste : ∀ A, M₀.map (cP'.hom.app A) ≫ sqR.hom.app A =
      sq₂.hom.app (F₀'.obj A) ≫ G₀.map (sq.hom.app A) ≫ cP.hom.app (K₀.obj A)) (A : C₁) :
    M.map (d'.hom.app A) ≫ (squareIsoTransport iP' iP iK iM sqR).hom.app A =
      (squareIsoTransport iG' iG iL iM sq₂).hom.app (F'.obj A) ≫
        G.map ((squareIsoTransport iF' iF iK iL sq).hom.app A) ≫ d.hom.app (K.obj A) := by
  have hdinv : d'.hom.app A ≫ iP'.inv.app A =
      G'.map (iF'.inv.app A) ≫ iG'.inv.app (F₀'.obj A) ≫ cP'.hom.app A := by
    rw [← cancel_mono (iP'.hom.app A), Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, hc', Iso.inv_hom_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  have hN := iM.hom.naturality (d'.hom.app A)
  have hIG' := iG'.inv.naturality (iF'.inv.app A)
  have hS := sq₂.hom.naturality (iF'.inv.app A)
  have hd := d.hom.naturality (iK.inv.app A)
  have hIG₁ := iG.hom.naturality (L₀.map (iF'.inv.app A))
  have hIG₂ := iG.hom.naturality (sq.hom.app A)
  simp only [Functor.comp_obj, Functor.comp_map] at hN hIG' hS hd hIG₁ hIG₂
  simp only [squareIsoTransport_hom_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hN, ← M₀.map_comp_assoc, hdinv, M₀.map_comp, M₀.map_comp, Category.assoc,
    Category.assoc, reassoc_of% hpaste, ← M₀.map_comp_assoc, hIG', M₀.map_comp, Category.assoc,
    reassoc_of% hS, reassoc_of% hc, ← hd, map_inv_app_hom_app_assoc G iL,
    ← reassoc_of% hIG₁,
    ← reassoc_of% hIG₂]

end Transport

section Faithful

/-! ### Transporting the pasting of squares along faithful functors -/

variable {𝓜₁ : Type*} [Category* 𝓜₁] {𝓜₂ : Type*} [Category* 𝓜₂] {𝓜₃ : Type*} [Category* 𝓜₃]
  {𝓜₄ : Type*} [Category* 𝓜₄] {𝓜₅ : Type*} [Category* 𝓜₅] {𝓜₆ : Type*} [Category* 𝓜₆]
  {𝓐₁ : Type*} [Category* 𝓐₁] {𝓐₂ : Type*} [Category* 𝓐₂] {𝓐₃ : Type*} [Category* 𝓐₃]
  {𝓐₄ : Type*} [Category* 𝓐₄] {𝓐₅ : Type*} [Category* 𝓐₅] {𝓐₆ : Type*} [Category* 𝓐₆]
  {φ₁ : 𝓜₁ ⥤ 𝓐₁} {φ₂ : 𝓜₂ ⥤ 𝓐₂} {φ₃ : 𝓜₃ ⥤ 𝓐₃} {φ₄ : 𝓜₄ ⥤ 𝓐₄} {φ₅ : 𝓜₅ ⥤ 𝓐₅}
  {φ₆ : 𝓜₆ ⥤ 𝓐₆}
  {F'ₘ : 𝓜₁ ⥤ 𝓜₃} {Fₘ : 𝓜₂ ⥤ 𝓜₄} {Kₘ : 𝓜₁ ⥤ 𝓜₂} {Lₘ : 𝓜₃ ⥤ 𝓜₄} {G'ₘ : 𝓜₃ ⥤ 𝓜₅}
  {Gₘ : 𝓜₄ ⥤ 𝓜₆} {Mₘ : 𝓜₅ ⥤ 𝓜₆} {P'ₘ : 𝓜₁ ⥤ 𝓜₅} {Pₘ : 𝓜₂ ⥤ 𝓜₆}
  {F' : 𝓐₁ ⥤ 𝓐₃} {F : 𝓐₂ ⥤ 𝓐₄} {K : 𝓐₁ ⥤ 𝓐₂} {L : 𝓐₃ ⥤ 𝓐₄} {G' : 𝓐₃ ⥤ 𝓐₅}
  {G : 𝓐₄ ⥤ 𝓐₆} {M : 𝓐₅ ⥤ 𝓐₆} {P' : 𝓐₁ ⥤ 𝓐₅} {P : 𝓐₂ ⥤ 𝓐₆}

/-- **Vertical pasting is reflected by faithful functors.** Suppose functors `Xₘ` between
categories `𝓜ᵢ` are lifts of functors `X` between categories `𝓐ᵢ` along functors
`φᵢ : 𝓜ᵢ ⥤ 𝓐ᵢ`, through isomorphisms `ηX : Xₘ ⋙ φ ≅ φ ⋙ X`, and that isomorphisms of squares
and of composites `eₘ`, `dₘ` lift isomorphisms `e`, `d` in the sense that `φ` takes their
components to those of `e`, `d` conjugated by the `η`. If `φ₆` is faithful and the isomorphisms
`e`, `d` paste, so do their lifts. -/
lemma vertical_paste_of_faithful [φ₆.Faithful]
    (ηF' : F'ₘ ⋙ φ₃ ≅ φ₁ ⋙ F') (ηF : Fₘ ⋙ φ₄ ≅ φ₂ ⋙ F) (ηK : Kₘ ⋙ φ₂ ≅ φ₁ ⋙ K)
    (ηL : Lₘ ⋙ φ₄ ≅ φ₃ ⋙ L) (ηG' : G'ₘ ⋙ φ₅ ≅ φ₃ ⋙ G') (ηG : Gₘ ⋙ φ₆ ≅ φ₄ ⋙ G)
    (ηM : Mₘ ⋙ φ₆ ≅ φ₅ ⋙ M) (ηP' : P'ₘ ⋙ φ₅ ≅ φ₁ ⋙ P') (ηP : Pₘ ⋙ φ₆ ≅ φ₂ ⋙ P)
    (e₁ₘ : F'ₘ ⋙ Lₘ ≅ Kₘ ⋙ Fₘ) (e₂ₘ : G'ₘ ⋙ Mₘ ≅ Lₘ ⋙ Gₘ) (eₘ : P'ₘ ⋙ Mₘ ≅ Kₘ ⋙ Pₘ)
    (d'ₘ : F'ₘ ⋙ G'ₘ ≅ P'ₘ) (dₘ : Fₘ ⋙ Gₘ ≅ Pₘ)
    (e₁ : F' ⋙ L ≅ K ⋙ F) (e₂ : G' ⋙ M ≅ L ⋙ G) (e : P' ⋙ M ≅ K ⋙ P) (d' : F' ⋙ G' ≅ P')
    (d : F ⋙ G ≅ P)
    (he₁ : ∀ A, φ₄.map (e₁ₘ.hom.app A) = ηL.hom.app (F'ₘ.obj A) ≫ L.map (ηF'.hom.app A) ≫
      e₁.hom.app (φ₁.obj A) ≫ F.map (ηK.inv.app A) ≫ ηF.inv.app (Kₘ.obj A))
    (he₂ : ∀ A, φ₆.map (e₂ₘ.hom.app A) = ηM.hom.app (G'ₘ.obj A) ≫ M.map (ηG'.hom.app A) ≫
      e₂.hom.app (φ₃.obj A) ≫ G.map (ηL.inv.app A) ≫ ηG.inv.app (Lₘ.obj A))
    (he : ∀ A, φ₆.map (eₘ.hom.app A) = ηM.hom.app (P'ₘ.obj A) ≫ M.map (ηP'.hom.app A) ≫
      e.hom.app (φ₁.obj A) ≫ P.map (ηK.inv.app A) ≫ ηP.inv.app (Kₘ.obj A))
    (hd' : ∀ A, φ₅.map (d'ₘ.hom.app A) = ηG'.hom.app (F'ₘ.obj A) ≫ G'.map (ηF'.hom.app A) ≫
      d'.hom.app (φ₁.obj A) ≫ ηP'.inv.app A)
    (hd : ∀ A, φ₆.map (dₘ.hom.app A) = ηG.hom.app (Fₘ.obj A) ≫ G.map (ηF.hom.app A) ≫
      d.hom.app (φ₂.obj A) ≫ ηP.inv.app A)
    (h : ∀ A, M.map (d'.hom.app A) ≫ e.hom.app A =
      e₂.hom.app (F'.obj A) ≫ G.map (e₁.hom.app A) ≫ d.hom.app (K.obj A)) (A : 𝓜₁) :
    Mₘ.map (d'ₘ.hom.app A) ≫ eₘ.hom.app A =
      e₂ₘ.hom.app (F'ₘ.obj A) ≫ Gₘ.map (e₁ₘ.hom.app A) ≫ dₘ.hom.app (Kₘ.obj A) := by
  apply φ₆.map_injective
  have hM := ηM.hom.naturality (d'ₘ.hom.app A)
  have hG := ηG.hom.naturality (e₁ₘ.hom.app A)
  have n₁ := e₂.hom.naturality (ηF'.hom.app A)
  have n₂ := d.hom.naturality (ηK.inv.app A)
  simp only [Functor.comp_obj, Functor.comp_map] at hM hG n₁ n₂
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, he, he₂, hd, reassoc_of% hM, hd']
  simp only [Category.assoc]
  rw [reassoc_of% hG, Iso.inv_hom_id_app_assoc, he₁]
  simp only [Functor.map_comp, Category.assoc]
  rw [map_inv_app_hom_app_assoc M ηP', map_inv_app_hom_app_assoc G ηL,
    map_inv_app_hom_app_assoc G ηF, ← reassoc_of% n₁, reassoc_of% n₂, reassoc_of% (h (φ₁.obj A))]

end Faithful

section HomotopyCategory

/-! ### Square isomorphisms on homotopy categories -/

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] {C₂ : Type*} [Category* C₂] [Preadditive C₂]
  {C₃ : Type*} [Category* C₃] [Preadditive C₃] {C₄ : Type*} [Category* C₄] [Preadditive C₄]
  {C₅ : Type*} [Category* C₅] [Preadditive C₅] {C₆ : Type*} [Category* C₆] [Preadditive C₆]
  {ι : Type*} (c : ComplexShape ι)
  {F' : C₁ ⥤ C₃} {F : C₂ ⥤ C₄} {K : C₁ ⥤ C₂} {L : C₃ ⥤ C₄}
  [F'.Additive] [F.Additive] [K.Additive] [L.Additive]

/-- The isomorphism of a square of additive functors, induced on homotopy categories. -/
def homotopySquareIso (e : F' ⋙ L ≅ K ⋙ F) :
    F'.mapHomotopyCategory c ⋙ L.mapHomotopyCategory c ≅
      K.mapHomotopyCategory c ⋙ F.mapHomotopyCategory c :=
  Functor.mapHomotopyCategoryCompIso e c ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (K ⋙ F)) c).symm

/-- The component of `homotopySquareIso c e` at `X` is the image in the homotopy category of
the component of `e.hom` on the complex `X.as`. -/
lemma homotopySquareIso_hom_app (e : F' ⋙ L ≅ K ⋙ F) (X : HomotopyCategory C₁ c) :
    (homotopySquareIso c e).hom.app X =
      (HomotopyCategory.quotient C₄ c).map ((NatTrans.mapHomologicalComplex e.hom c).app X.as) := by
  have h' : (Functor.mapHomotopyCategoryCompIso (Iso.refl (K ⋙ F)) c).inv.app X =
      (HomotopyCategory.quotient C₄ c).map
        ((NatTrans.mapHomologicalComplex (Iso.refl (K ⋙ F)).inv c).app X.as) := rfl
  simp only [Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id] at h'
  simp only [homotopySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    mapHomotopyCategoryCompIso_hom_app, h']
  exact Category.comp_id _

variable {G' : C₃ ⥤ C₅} {G : C₄ ⥤ C₆} {M : C₅ ⥤ C₆} {P' : C₁ ⥤ C₅} {P : C₂ ⥤ C₆}
  [G'.Additive] [G.Additive] [M.Additive] [P'.Additive] [P.Additive]

/-- Vertical pasting of square isomorphisms is inherited by the induced square isomorphisms of
homotopy categories. -/
lemma homotopySquareIso_vertical_paste (e₁ : F' ⋙ L ≅ K ⋙ F) (e₂ : G' ⋙ M ≅ L ⋙ G)
    (e : P' ⋙ M ≅ K ⋙ P) (d' : F' ⋙ G' ≅ P') (d : F ⋙ G ≅ P)
    (h : ∀ A, M.map (d'.hom.app A) ≫ e.hom.app A =
      e₂.hom.app (F'.obj A) ≫ G.map (e₁.hom.app A) ≫ d.hom.app (K.obj A))
    (X : HomotopyCategory C₁ c) :
    (M.mapHomotopyCategory c).map ((Functor.mapHomotopyCategoryCompIso d' c).hom.app X) ≫
        (homotopySquareIso c e).hom.app X =
      (homotopySquareIso c e₂).hom.app ((F'.mapHomotopyCategory c).obj X) ≫
        (G.mapHomotopyCategory c).map ((homotopySquareIso c e₁).hom.app X) ≫
        (Functor.mapHomotopyCategoryCompIso d c).hom.app ((K.mapHomotopyCategory c).obj X) := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [homotopySquareIso_hom_app, mapHomotopyCategoryCompIso_hom_app,
    HomotopyCategory.quotient_obj_as]
  change (HomotopyCategory.quotient C₆ c).map ((M.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex d'.hom c).app X)) ≫
      (HomotopyCategory.quotient C₆ c).map ((NatTrans.mapHomologicalComplex e.hom c).app X) =
    (HomotopyCategory.quotient C₆ c).map
        ((NatTrans.mapHomologicalComplex e₂.hom c).app ((F'.mapHomologicalComplex c).obj X)) ≫
      (HomotopyCategory.quotient C₆ c).map ((G.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex e₁.hom c).app X)) ≫
      (HomotopyCategory.quotient C₆ c).map
        ((NatTrans.mapHomologicalComplex d.hom c).app ((K.mapHomologicalComplex c).obj X))
  simp only [← Functor.map_comp]
  congr 1
  ext n
  simpa using h (X.X n)

end HomotopyCategory

section KInjective

universe w v u wD

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w, v, u} C]
  [HasDerivedCategory.{wD} C] {H : Type*} [Category* H] {H' : Type*} [Category* H']

/-- Over a Grothendieck abelian category, a right derived functor on the unbounded derived
category stays one after composition with an arbitrary functor: both are computed by K-injective
complexes, at which the unit of the first, hence also its image under the functor, is an
isomorphism. In particular the instance needed by `squareMap` holds whenever the source of the
square is Grothendieck abelian. -/
theorem isRightDerivedFunctor_comp_right (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory C ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (G : H ⥤ H') :
    (RF ⋙ G).IsRightDerivedFunctor (whiskerUnit α G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (Stacks.Injectives.exists_kInjective_resolution_of_grothendieck (C := C)) (F ⋙ G) (RF ⋙ G) _
    fun I _ => ?_
  have := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective F RF α I
  simp only [whiskerUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]
  infer_instance

omit [IsGrothendieckAbelian.{w, v, u} C] [HasDerivedCategory.{wD} C] in
/-- **The comparison `R(G ∘ F) ⟶ RG ∘ RF` is an isomorphism when `F` preserves K-injective
complexes** ([Stacks, Tag 05T2] with the acyclicity supplied by K-injectivity): at a K-injective
complex `I` the units of `RP` at `I`, of `RF` at `I` and of `RG` at `F(I)` are isomorphisms, and
the comparison is determined by them; every object of the derived category is represented by a
K-injective complex. -/
theorem isIso_compComparison_of_isKInjective
    {C₁ : Type*} [Category* C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
    [HasDerivedCategory C₁]
    {C₂ : Type*} [Category* C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
    [HasDerivedCategory C₂]
    {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (P : C₁ ⥤ C₃) [F.Additive] [G.Additive] [P.Additive]
    (d : F ⋙ G ≅ P)
    {RF : DerivedCategory C₁ ⥤ DerivedCategory C₂} {RG : DerivedCategory C₂ ⥤ DerivedCategory C₃}
    {RP : DerivedCategory C₁ ⥤ DerivedCategory C₃}
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αP : P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ))]
    [RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))]
    (hF : ∀ (I : CochainComplex C₁ ℤ), I.IsKInjective →
      CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsIso (compComparison (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) αF αG αP
      (Functor.mapHomotopyCategoryCompIso d (ComplexShape.up ℤ))) := by
  apply Stacks.Injectives.isIso_natTrans_of_kInjective
  intro I hI
  have h := compComparison_fac_app (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) αF αG αP
    (Functor.mapHomotopyCategoryCompIso d (ComplexShape.up ℤ))
    ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj I)
  have := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ RP αP I
  have := Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ RF αF I
  have := hF I hI
  have : IsIso (αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective _ RG αG
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hR : IsIso (αP.app ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj I) ≫
      (compComparison (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) αF αG αP
        (Functor.mapHomotopyCategoryCompIso d (ComplexShape.up ℤ))).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj I))) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (αP.app ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj I)) _

end KInjective

end Stacks.DerivedBaseChange

end
