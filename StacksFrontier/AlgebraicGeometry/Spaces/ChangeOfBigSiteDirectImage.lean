module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFull
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMap

/-!
# Direct images of affine morphisms after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, `X` an algebraic space over `S`
defined using `B`, and `Y` an algebraic space affine over `X`. Enlarging the site gives an
algebraic space `Y'` affine over `X'` (`AlgebraicGeometry.Space.changeBigSiteAffineOver`). This
file identifies the direct image `π'_* 𝒪_{Y'}`, read on the étale charts of `X`, with `π_* 𝒪_Y`.

Over an étale chart `U` of `X` the sections of `π_* 𝒪_Y` are the regular functions on the base
change `Y ×_X U` (Stacks 03G8, `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`), and the
sections of `π'_* 𝒪_{Y'}` over the transport of `U` are the regular functions on `Y' ×_{X'} U`;
the two base changes are the same scheme, the transport of a cartesian square being cartesian
(`AlgebraicGeometry.Space.isPullback_changeBigSiteChart`).

## Main definitions

* `AlgebraicGeometry.Space.changeBigSiteAffineOver`: enlarging the site, on algebraic spaces
  affine over `X`.
* `AlgebraicGeometry.Space.changeBigSiteBaseChangeIso`: the base change of `Y'` along a
  transported chart is the base change of `Y` along the chart.
* `AlgebraicGeometry.Space.changeBigSitePushforwardAlgebraIso`: the restriction of `π'_* 𝒪_{Y'}`
  to the charts of `X` is `π_* 𝒪_Y`.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Enlarging the big fppf site, on algebraic spaces affine over `X`.** -/
def changeBigSiteAffineOver :
    AffineOver B S hS X ⥤ AffineOver B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.post (changeBigSite B B' h S hS))
    (fun Y => isAffineHom_changeBigSite_map B B' h S hS X Y.obj.hom Y.property)

variable {X} (Y : AffineOver B S hS X)

/-- The structure morphism of an algebraic space affine over `X` is representable. -/
abbrev affineOverRep : yoneda.relativelyRepresentable Y.obj.hom.hom :=
  relativelyRepresentable_of_isAffineHom B S hS Y.obj.hom Y.property

/-- The structure morphism of its enlargement is representable. -/
abbrev changeBigSiteAffineOverRep :
    yoneda.relativelyRepresentable ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj.hom.hom :=
  relativelyRepresentable_of_isAffineHom B' S (BigFppfSite.contains_of_isContained h hS)
    ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj.hom
    ((changeBigSiteAffineOver B B' h S hS X).obj Y).property

/-- The transport of the cartesian square defining the base change of `Y` along a chart. -/
theorem isPullback_changeBigSiteAffineOver (U : SmallEtale B S hS X.obj) :
    IsPullback (changeBigSiteChart B B' h S hS Y.obj.left
        (CostructuredArrow.mk ((affineOverRep B S hS Y).fst U.obj.hom))).hom
      (yoneda.map ((inclusionOver h S hS).map ((affineOverRep B S hS Y).snd U.obj.hom)))
      ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj.hom.hom
      ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom :=
  isPullback_changeBigSiteChart B B' h S hS Y.obj.hom _ _ _
    ((affineOverRep B S hS Y).isPullback U.obj.hom)

/-- **The base change of `Y'` along a transported chart is the base change of `Y` along the
chart.** -/
def changeBigSiteBaseChangeIso (U : SmallEtale B S hS X.obj) :
    (inclusionOver h S hS).obj ((affineOverRep B S hS Y).pullback U.obj.hom) ≅
      (changeBigSiteAffineOverRep B B' h S hS Y).pullback
        ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom :=
  yoneda.preimageIso ((isPullback_changeBigSiteAffineOver B B' h S hS Y U).isoIsPullback _ _
    ((changeBigSiteAffineOverRep B B' h S hS Y).isPullback _))

/-- The `appTop` of a functor to schemes turns a factorization into the reversed factorization. -/
private theorem appTop_map_comp_eq {C : Type*} [Category C] (K : C ⥤ Scheme.{u}) {P Q R : C}
    (p : P ⟶ Q) (q : Q ⟶ R) {r : P ⟶ R} (h : p ≫ q = r) :
    (K.map q).appTop ≫ (K.map p).appTop = (K.map r).appTop := by
  rw [← h, K.map_comp, Scheme.Hom.comp_appTop]

/-- The identification `changeBigSiteBaseChangeIso` commutes with the projections to the chart. -/
theorem changeBigSiteBaseChangeIso_hom_snd (U : SmallEtale B S hS X.obj) :
    (changeBigSiteBaseChangeIso B B' h S hS Y U).hom ≫
        (changeBigSiteAffineOverRep B B' h S hS Y).snd
          ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom =
      (inclusionOver h S hS).map ((affineOverRep B S hS Y).snd U.obj.hom) := by
  apply yoneda.map_injective
  refine (yoneda.map_comp _ _).trans ?_
  refine (congrArg (· ≫ _) (yoneda.map_preimage _)).trans ?_
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The identification `changeBigSiteBaseChangeIso` carries the projection to `Y'` to the
transport of the projection to `Y`. -/
theorem changeBigSiteBaseChangeIso_hom_fst (U : SmallEtale B S hS X.obj) :
    yoneda.map (changeBigSiteBaseChangeIso B B' h S hS Y U).hom ≫
        (changeBigSiteAffineOverRep B B' h S hS Y).fst
          ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom =
      (changeBigSiteChart B B' h S hS Y.obj.left
        (CostructuredArrow.mk ((affineOverRep B S hS Y).fst U.obj.hom))).hom := by
  refine (congrArg (· ≫ _) (yoneda.map_preimage _)).trans ?_
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The sections of `π'_* 𝒪_{Y'}` over a transported chart are the sections of `π_* 𝒪_Y`
over the chart**: both are the regular functions on the same base change (Stacks 03G8). -/
def changeBigSitePushforwardSectionsIso (U : SmallEtale B S hS X.obj) :
    (pushforwardAlgebra B' S (BigFppfSite.contains_of_isContained h hS)
        ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj).right.obj.obj
        (op ((changeBigSiteSmallEtale B B' h S hS X).obj U)) ≅
      (pushforwardAlgebra B S hS Y.obj).right.obj.obj (op U) :=
  pushforwardAlgebraSectionsIso B' S (BigFppfSite.contains_of_isContained h hS) _
      (changeBigSiteAffineOverRep B B' h S hS Y) _ ≪≫
    Scheme.Γ.mapIso ((BigFppfOver.toScheme B' S (BigFppfSite.contains_of_isContained h hS)).mapIso
      (changeBigSiteBaseChangeIso B B' h S hS Y U)).op ≪≫
    (pushforwardAlgebraSectionsIso B S hS Y.obj (affineOverRep B S hS Y) U).symm

/-- The identification of sections is compatible with the structure maps from `𝒪_X`. -/
theorem fSharp_app_comp_changeBigSitePushforwardSectionsIso (U : SmallEtale B S hS X.obj) :
    (smallEtaleRingedToposHom B' S (BigFppfSite.contains_of_isContained h hS)
        ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj.hom).fSharp.hom.app
          (op ((changeBigSiteSmallEtale B B' h S hS X).obj U)) ≫
        (changeBigSitePushforwardSectionsIso B B' h S hS Y U).hom =
      (smallEtaleRingedToposHom B S hS Y.obj.hom).fSharp.hom.app (op U) := by
  have h1 := fSharp_app_comp_pushforwardAlgebraSectionsIso B' S
    (BigFppfSite.contains_of_isContained h hS) ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj
    (changeBigSiteAffineOverRep B B' h S hS Y) ((changeBigSiteSmallEtale B B' h S hS X).obj U)
  have h2 := fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Y.obj
    (affineOverRep B S hS Y) U
  have h3 := changeBigSiteBaseChangeIso_hom_snd B B' h S hS Y U
  have h4 := appTop_map_comp_eq
    (BigFppfOver.toScheme B' S (BigFppfSite.contains_of_isContained h hS)) _ _ h3
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (pushforwardAlgebraSectionsIso B S hS Y.obj
    (affineOverRep B S hS Y) U).inv) h4).trans ?_
  refine (congrArg (· ≫ (pushforwardAlgebraSectionsIso B S hS Y.obj
    (affineOverRep B S hS Y) U).inv) h2.symm).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
    (Category.comp_id _))

private theorem conj_comp_eq' {C : Type*} [Category C] {P Q P' Q' T T' : C} (e : P ≅ Q)
    (x : P ⟶ P') (e' : P' ≅ Q') {s' : Q' ⟶ T'} {j' : P' ⟶ T'} {s : Q ⟶ T} {j : P ⟶ T}
    {kk : T ⟶ T'} (h1 : e'.hom ≫ s' = j') (h2 : x ≫ j' = j ≫ kk) (h3 : e.hom ≫ s = j) :
    (e.inv ≫ x ≫ e'.hom) ≫ s' = s ≫ kk := by
  rw [Category.assoc, Category.assoc, h1, h2, ← h3, Category.assoc, Iso.inv_hom_id_assoc]

/-- A morphism conjugated by isomorphisms, mapped by a functor and composed with `f'`, is `f`. -/
private theorem conj_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q P' Q' : C}
    {Z : D} (e : P ≅ Q) (x : P ⟶ P') (e' : P' ≅ Q') {f : F.obj Q ⟶ Z} {f' : F.obj Q' ⟶ Z}
    {c : F.obj P ⟶ Z} {c' : F.obj P' ⟶ Z} (h1 : F.map e'.hom ≫ f' = c') (h2 : F.map x ≫ c' = c)
    (h3 : F.map e.hom ≫ f = c) : F.map (e.inv ≫ x ≫ e'.hom) ≫ f' = f := by
  simpa using conj_comp_eq' (F.mapIso e) (F.map x) (F.mapIso e') (kk := 𝟙 _) h1
    (by simpa using h2) h3

/-- The base change along a morphism of charts, compared through the identifications of base
changes. -/
theorem changeBigSiteBaseChangeIso_naturality {U V : SmallEtale B S hS X.obj} (k : U ⟶ V) :
    let a := ((smallBaseChange B S hS Y.obj.hom (affineOverRep B S hS Y)).map k).hom.left
    let a' := (changeBigSiteBaseChangeIso B B' h S hS Y U).inv ≫ (inclusionOver h S hS).map a ≫
      (changeBigSiteBaseChangeIso B B' h S hS Y V).hom
    yoneda.map a' ≫ (changeBigSiteAffineOverRep B B' h S hS Y).fst
        ((changeBigSiteSmallEtale B B' h S hS X).obj V).obj.hom =
      (changeBigSiteAffineOverRep B B' h S hS Y).fst
        ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom ∧
    a' ≫ (changeBigSiteAffineOverRep B B' h S hS Y).snd
        ((changeBigSiteSmallEtale B B' h S hS X).obj V).obj.hom =
      (changeBigSiteAffineOverRep B B' h S hS Y).snd
        ((changeBigSiteSmallEtale B B' h S hS X).obj U).obj.hom ≫
        ((changeBigSiteSmallEtale B B' h S hS X).map k).hom.left := by
  intro a a'
  have ha₁ := smallBaseChange_map_fst B S hS Y.obj.hom (affineOverRep B S hS Y) k
  have ha₂ := smallBaseChange_map_snd B S hS Y.obj.hom (affineOverRep B S hS Y) k
  let m : CostructuredArrow.mk ((affineOverRep B S hS Y).fst U.obj.hom) ⟶
      CostructuredArrow.mk ((affineOverRep B S hS Y).fst V.obj.hom) :=
    CostructuredArrow.homMk a ha₁
  refine ⟨conj_comp_eq yoneda _ _ _ (changeBigSiteBaseChangeIso_hom_fst B B' h S hS Y V)
      (changeBigSiteChart_w B B' h S hS Y.obj.left m)
      (changeBigSiteBaseChangeIso_hom_fst B B' h S hS Y U),
    conj_comp_eq' _ _ _ (changeBigSiteBaseChangeIso_hom_snd B B' h S hS Y V) ?_
      (changeBigSiteBaseChangeIso_hom_snd B B' h S hS Y U)⟩
  exact ((inclusionOver h S hS).map_comp _ _).symm.trans
    ((congrArg (inclusionOver h S hS).map ha₂).trans ((inclusionOver h S hS).map_comp _ _))

private theorem conj_naturality {C : Type*} [Category C] {M'V M'U GV GU ΓV ΓU MV MU : C}
    (m' : M'V ⟶ M'U) (s'U : M'U ⟶ GU) (s'V : M'V ⟶ GV) (a'Γ : GV ⟶ GU) (eU : GU ⟶ ΓU)
    (eV : GV ⟶ ΓV) (aΓ : ΓV ⟶ ΓU) (sU : MU ≅ ΓU) (sV : MV ≅ ΓV) (m : MV ⟶ MU)
    (hN' : m' ≫ s'U = s'V ≫ a'Γ) (hΓ : a'Γ ≫ eU = eV ≫ aΓ) (hN : m ≫ sU.hom = sV.hom ≫ aΓ) :
    m' ≫ s'U ≫ eU ≫ sU.inv = (s'V ≫ eV ≫ sV.inv) ≫ m := by
  have hm : aΓ ≫ sU.inv = sV.inv ≫ m := by
    rw [Iso.eq_inv_comp, ← reassoc_of% hN, Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% hN', reassoc_of% hΓ, hm]
  simp only [Category.assoc]

/-- **The identification of sections is natural in the chart.** -/
theorem changeBigSitePushforwardSectionsIso_naturality {U V : SmallEtale B S hS X.obj}
    (k : U ⟶ V) :
    (pushforwardAlgebra B' S (BigFppfSite.contains_of_isContained h hS)
        ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj).right.obj.map
          ((changeBigSiteSmallEtale B B' h S hS X).map k).op ≫
        (changeBigSitePushforwardSectionsIso B B' h S hS Y U).hom =
      (changeBigSitePushforwardSectionsIso B B' h S hS Y V).hom ≫
        (pushforwardAlgebra B S hS Y.obj).right.obj.map k.op := by
  obtain ⟨h1, h2⟩ := changeBigSiteBaseChangeIso_naturality B B' h S hS Y k
  let a := ((smallBaseChange B S hS Y.obj.hom (affineOverRep B S hS Y)).map k).hom.left
  have hN' := pushforwardAlgebraSectionsIso_naturality B' S
    (BigFppfSite.contains_of_isContained h hS) ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj
    (changeBigSiteAffineOverRep B B' h S hS Y) ((changeBigSiteSmallEtale B B' h S hS X).map k) _
    h1 h2
  have hN := pushforwardAlgebraSectionsIso_naturality B S hS Y.obj (affineOverRep B S hS Y) k a
    (smallBaseChange_map_fst B S hS Y.obj.hom (affineOverRep B S hS Y) k)
    (smallBaseChange_map_snd B S hS Y.obj.hom (affineOverRep B S hS Y) k)
  let eU := changeBigSiteBaseChangeIso B B' h S hS Y U
  let eV := changeBigSiteBaseChangeIso B B' h S hS Y V
  let K' := BigFppfOver.toScheme B' S (BigFppfSite.contains_of_isContained h hS)
  have hcomp : eU.hom ≫ (eU.inv ≫ (inclusionOver h S hS).map a ≫ eV.hom) =
      (inclusionOver h S hS).map a ≫ eV.hom := Iso.hom_inv_id_assoc _ _
  have hΓ := (appTop_map_comp_eq K' _ _ hcomp).trans
    (appTop_map_comp_eq K' ((inclusionOver h S hS).map a) eV.hom rfl).symm
  exact conj_naturality _ _ _ _ _ _ _ _ _ _ hN' hΓ hN

/-- **The restriction of `π'_* 𝒪_{Y'}` to the étale charts of `X` is `π_* 𝒪_Y`**, as sheaves of
`𝒪_X`-algebras. -/
def changeBigSitePushforwardAlgebraIso :
    AlgebraSheaf.changeBigSiteRestrict B B' h S hS X
        (pushforwardAlgebra B' S (BigFppfSite.contains_of_isContained h hS)
          ((changeBigSiteAffineOver B B' h S hS X).obj Y).obj) ≅
      pushforwardAlgebra B S hS Y.obj :=
  AlgebraSheaf.isoOfRight B S hS
    ((fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
      (fun U => changeBigSitePushforwardSectionsIso B B' h S hS Y U.unop)
      (fun {_ _} k => changeBigSitePushforwardSectionsIso_naturality B B' h S hS Y k.unop)))
    (fun U r => (CommRingCat.comp_apply _ _ r).symm.trans (ConcreteCategory.congr_hom
      (fSharp_app_comp_changeBigSitePushforwardSectionsIso B B' h S hS Y U.unop) r))

end AlgebraicGeometry.Space

end
