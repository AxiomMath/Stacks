module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicityFull
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.FamilyPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.HomDescent

/-!
# The pullback functor for a morphism of families is the pullback functor for the coproducts

A morphism of families of algebraic spaces with fixed target induces a morphism of the
coproducts of the sources, hence a commutative square of single morphisms. Under the
equivalences of Tag 0ADK, the pullback functor on descent data for the families, Tag 0ADN,
becomes the pullback functor for that square, Tag 0ADL.

## Main definitions

* `AlgebraicGeometry.Space.Descent.coproductMap` is the morphism of coproducts of the sources
  induced by a morphism of families.

## Main results

* `AlgebraicGeometry.Space.Descent.coproductMap_comm`: the induced morphism of coproducts
  completes the square of structure morphisms over the given morphism of targets.
* `AlgebraicGeometry.Space.Descent.isPullback_totalCoproduct`: a coproduct of base changes is
  the base change of the coproduct.
* `AlgebraicGeometry.Space.Descent.PulledBackDatum.ofIso`: a descent datum isomorphic to a
  pulled-back datum is itself a pulled-back datum.
* `AlgebraicGeometry.Space.Descent.pullbackFunctorCoproductComparison` is Tag 0ADN part (4):
  the pullback functor along a morphism of families agrees, through the equivalences of
  Tag 0ADK, with the pullback functor of Tag 0ADL for the induced square of coproducts. The
  isomorphism is pinned on each summand of the coproduct, where it is the projection of the
  pulled-back component onto the original component.

## Implementation notes

`AlgebraicGeometry.Space.Descent.isPullback_totalCoproduct` is proved from
`AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`, which says that pulling a
coproduct of fppf sheaves back decomposes the source as a coproduct, together with
`AlgebraicGeometry.Space.Descent.isPullback_coproduct_map`, which exhibits a summand as the
base change of a summand of the target.

## References

* [Stacks Project, Tag 0ADN](https://stacks.math.columbia.edu/tag/0ADN)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
* [Stacks Project, Tag 0ADL](https://stacks.math.columbia.edu/tag/0ADL)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v v' w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} [Small.{u} ι] [B.AdmitsCoproductIndex ι]
variable {ι' : Type v'} [Small.{u} ι'] [B.AdmitsCoproductIndex ι']
variable {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {X' : ι' → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T) (f' : ∀ i, X' i ⟶ T')
variable (hT : IsAlgebraicSpace B S hS T) (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
variable (hT' : IsAlgebraicSpace B S hS T') (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i))
variable (α : ι' → ι) (g : T' ⟶ T) (gᵢ : ∀ i, X' i ⟶ X (α i))
variable (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)
variable (Ycop : AlgebraicSheafCoproduct X hX) (Y'cop : AlgebraicSheafCoproduct X' hX')

/-- The morphism of sheaf coproducts of the sources induced by a morphism of families of
algebraic spaces with fixed target. -/
public def coproductMap : Y'cop.sheaf.obj ⟶ Ycop.sheaf.obj :=
  Y'cop.desc Ycop.sheaf (fun i ↦ gᵢ i ≫ (Ycop.ι (α i)).hom)

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
/-- The induced morphism of coproducts restricts to the given component map on each
summand. -/
@[reassoc (attr := simp)]
public lemma ι_coproductMap (i : ι') :
    (Y'cop.ι i).hom ≫ coproductMap hX hX' α gᵢ Ycop Y'cop = gᵢ i ≫ (Ycop.ι (α i)).hom :=
  Y'cop.ι_desc _ _ i

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
include comm in
/-- **The induced morphism of coproducts completes the square of structure morphisms.** This
is the commutative square of single morphisms to which Tag 0ADL applies. -/
public lemma coproductMap_comm :
    coproductMap hX hX' α gᵢ Ycop Y'cop ≫ Ycop.desc (spaceSheaf T hT) f =
      Y'cop.desc (spaceSheaf T' hT') f' ≫ g := by
  refine Y'cop.desc_ext (spaceSheaf T hT) (fun i ↦ ?_)
  simp only [ι_coproductMap_assoc, AlgebraicSheafCoproduct.ι_desc,
    AlgebraicSheafCoproduct.ι_desc_assoc]
  exact comm i

/-- **A coproduct of base changes is the base change of the coproduct.** If each object of a
descent datum for the second family sits in a pullback square over the corresponding component
map of the morphism of families, then the sheaf coproduct of those objects sits in a pullback
square over the induced morphism of coproducts. -/
public lemma isPullback_totalCoproduct (D : DescentData f hT hX) (E₁ : DescentData f' hT' hX')
    (m : ∀ i, (E₁.obj i).left ⟶ (D.obj (α i)).left)
    (hm : ∀ i, IsPullback (E₁.obj i).hom (m i) (gᵢ i) (D.obj (α i)).hom) :
    IsPullback
      ((fullTotalCoproduct f' hT' hX' E₁).desc (fullTotalCoproduct f hT hX D).sheaf
        (fun i ↦ m i ≫ ((fullTotalCoproduct f hT hX D).ι (α i)).hom))
      ((fullTotalCoproduct f' hT' hX' E₁).map Y'cop (fun i ↦ (E₁.obj i).hom))
      ((fullTotalCoproduct f hT hX D).map Ycop (fun j ↦ (D.obj j).hom))
      (coproductMap hX hX' α gᵢ Ycop Y'cop) := by
  let := BigFppfOver.hasSheafify_type B S hS
  set C := fullTotalCoproduct f hT hX D with hCdef
  set C' := fullTotalCoproduct f' hT' hX' E₁ with hC'def
  set v := C.map Ycop (fun j ↦ (D.obj j).hom) with hvdef
  set gt := coproductMap hX hX' α gᵢ Ycop Y'cop with hgtdef
  have hsummand : ∀ i : ι', (C.ι (α i)).hom ≫ v = (D.obj (α i)).hom ≫ (Ycop.ι (α i)).hom :=
    fun i ↦ AlgebraicSheafCoproduct.ι_map C Ycop (fun j ↦ (D.obj j).hom) (α i)
  have hbase : ∀ i : ι', (Y'cop.ι i).hom ≫ gt = gᵢ i ≫ (Ycop.ι (α i)).hom :=
    fun i ↦ ι_coproductMap hX hX' α gᵢ Ycop Y'cop i
  have hcomm : ∀ i : ι',
      (m i ≫ (C.ι (α i)).hom) ≫ v = ((E₁.obj i).hom ≫ (Y'cop.ι i).hom) ≫ gt := by
    intro i
    rw [Category.assoc, hsummand, Category.assoc, hbase, ← Category.assoc, ← Category.assoc,
      (hm i).w]
  have hsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback v gt) := by
    refine ObjectProperty.prop_limit (Presheaf.IsSheaf (BigFppfOver.topology B S hS))
      (cospan v gt) ?_
    rintro (_ | _ | _)
    all_goals
      first
        | exact Ycop.sheaf.property
        | exact C.sheaf.property
        | exact Y'cop.sheaf.property
  set p : ∀ i : ι', (E₁.obj i).left ⟶ pullback v gt := fun i ↦
    pullback.lift (m i ≫ (C.ι (α i)).hom) ((E₁.obj i).hom ≫ (Y'cop.ι i).hom) (hcomm i)
    with hpdef
  have hpfst : ∀ i : ι', p i ≫ pullback.fst v gt = m i ≫ (C.ι (α i)).hom :=
    fun i ↦ pullback.lift_fst _ _ _
  have hpsnd : ∀ i : ι', p i ≫ pullback.snd v gt = (E₁.obj i).hom ≫ (Y'cop.ι i).hom :=
    fun i ↦ pullback.lift_snd _ _ _
  have hpb : ∀ i : ι',
      IsPullback (p i) ((E₁.obj i).hom) (pullback.snd v gt) ((Y'cop.ι i).hom) := by
    intro i
    refine IsPullback.of_right ?_ (hpsnd i) (IsPullback.of_hasPullback v gt)
    rw [hpfst i, hbase i]
    exact (hm i).flip.paste_horiz
      (isPullback_coproduct_map _ C Ycop (fun j ↦ (D.obj j).hom) (α i))
  let Ash : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨pullback v gt, hsheaf⟩
  let psh : ∀ i : ι',
      spaceSheaf (E₁.obj i).left (E₁.obj_isAlgebraicSpace i) ⟶ Ash := fun i ↦ ⟨p i⟩
  have hcol : Nonempty (IsColimit (Cofan.mk Ash psh)) :=
    AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback B S hS Y'cop.ι
      Y'cop.isColimit (⟨pullback.snd v gt⟩ : Ash ⟶ Y'cop.sheaf) psh
      (fun i ↦ (⟨(E₁.obj i).hom⟩ : spaceSheaf (E₁.obj i).left (E₁.obj_isAlgebraicSpace i) ⟶
        spaceSheaf (X' i) (hX' i))) (fun i ↦
        IsPullback.of_map_of_faithful (sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
          (hpb i))
  let e : C'.sheaf ≅ Ash := IsColimit.coconePointUniqueUpToIso C'.isColimit hcol.some
  have he : ∀ i : ι', (C'.ι i).hom ≫ e.hom.hom = p i := by
    intro i
    have h : C'.ι i ≫ e.hom = psh i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom C'.isColimit hcol.some
        (j := (⟨i⟩ : Discrete ι'))
    show (C'.ι i ≫ e.hom).hom = p i
    rw [h]
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso e) ?_ ?_
  · refine C'.desc_ext Ycop.sheaf (fun i ↦ ?_)
    rw [← Category.assoc, AlgebraicSheafCoproduct.ι_desc, ← Category.assoc,
      AlgebraicSheafCoproduct.ι_map, Category.assoc, hsummand, Category.assoc, hbase,
      ← Category.assoc, ← Category.assoc, (hm i).w]
  · refine C'.desc_ext C.sheaf (fun i ↦ ?_)
    rw [← Category.assoc]
    show ((C'.ι i).hom ≫ e.hom.hom) ≫ pullback.fst v gt = _
    rw [he i, hpfst i, AlgebraicSheafCoproduct.ι_desc]
  · refine C'.desc_ext Y'cop.sheaf (fun i ↦ ?_)
    rw [← Category.assoc]
    show ((C'.ι i).hom ≫ e.hom.hom) ≫ pullback.snd v gt = _
    rw [he i, hpsnd i, AlgebraicSheafCoproduct.ι_map]

/-- The underlying isomorphism of algebraic spaces of a component of an isomorphism of descent
data. -/
public def descentIsoLeft {E₂ E₃ : DescentData f' hT' hX'} (e : E₂ ≅ E₃) (i : ι') :
    (E₂.obj i).left ≅ (E₃.obj i).left where
  hom := (e.hom.hom i).left
  inv := (e.inv.hom i).left
  hom_inv_id := by
    have h := congrArg (fun k : E₂ ⟶ E₂ ↦ (k.hom i).left) e.hom_inv_id
    simp only [DescentData.comp_hom, DescentData.id_hom, Over.comp_left, Over.id_left] at h
    exact h
  inv_hom_id := by
    have h := congrArg (fun k : E₃ ⟶ E₃ ↦ (k.hom i).left) e.inv_hom_id
    simp only [DescentData.comp_hom, DescentData.id_hom, Over.comp_left, Over.id_left] at h
    exact h

/-- **A descent datum isomorphic to a pulled-back datum is itself a pulled-back datum.** Its
component projections and gluing comparisons are those of the given one, precomposed with the
isomorphism. -/
public def PulledBackDatum.ofIso {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (E₂ : DescentData f' hT' hX')
    (e : E₂ ≅ Q.datum) : PulledBackDatum f f' hT hX hT' hX' α gᵢ D where
  datum := E₂
  objMap i := (e.hom.hom i).left ≫ Q.objMap i
  obj_isPullback i := by
    haveI : IsIso ((e.hom.hom i).left) := (descentIsoLeft f' hT' hX' e i).isIso_hom
    have hsq : IsPullback (E₂.obj i).hom ((e.hom.hom i).left) (𝟙 (X' i))
        ((Q.datum.obj i).hom) := by
      refine IsPullback.of_vert_isIso ⟨?_⟩
      simpa using (Over.w (e.hom.hom i)).symm
    simpa using hsq.paste_vert (Q.obj_isPullback i)
  source_eq_new _ _ := rfl
  source_eq_old i j := Q.source_eq_old i j
  target_eq_new _ _ := rfl
  target_eq_old i j := Q.target_eq_old i j
  gluingSourceMap i j :=
    (prod.map ((Over.map (f' i)).map (e.hom.hom i)) (𝟙 (Over.mk (f' j)))).left ≫
      Q.gluingSourceMap i j
  gluingSource_fst i j := by
    have h := congrArg Over.Hom.left
      (prod.map_fst ((Over.map (f' i)).map (e.hom.hom i)) (𝟙 (Over.mk (f' j))))
    simp only [Over.comp_left] at h
    rw [Category.assoc, Q.gluingSource_fst, ← Category.assoc, h]
    simp [Category.assoc]
  gluingSource_snd i j := by
    have h := congrArg Over.Hom.left
      (prod.map_snd ((Over.map (f' i)).map (e.hom.hom i)) (𝟙 (Over.mk (f' j))))
    simp only [Over.comp_left, Over.id_left, Category.comp_id] at h
    rw [Category.assoc, Q.gluingSource_snd, ← Category.assoc, h]
  gluingTargetMap i j :=
    (prod.map (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map (e.hom.hom j))).left ≫
      Q.gluingTargetMap i j
  gluingTarget_fst i j := by
    have h := congrArg Over.Hom.left
      (prod.map_fst (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map (e.hom.hom j)))
    simp only [Over.comp_left, Over.id_left, Category.comp_id] at h
    rw [Category.assoc, Q.gluingTarget_fst, ← Category.assoc, h]
  gluingTarget_snd i j := by
    have h := congrArg Over.Hom.left
      (prod.map_snd (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map (e.hom.hom j)))
    simp only [Over.comp_left] at h
    rw [Category.assoc, Q.gluingTarget_snd, ← Category.assoc, h]
    simp [Category.assoc]
  gluing_comm i j := by
    have hq := Q.gluing_comm i j
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hq ⊢
    have he := congrArg Over.Hom.left (e.hom.comm i j)
    simp only [Over.comp_left] at he
    rw [Category.assoc, hq, ← Category.assoc, he, Category.assoc]

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
/-- The descent datum underlying `PulledBackDatum.ofIso Q E₂ e` is `E₂`. -/
@[simp]
public lemma PulledBackDatum.ofIso_datum {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (E₂ : DescentData f' hT' hX')
    (e : E₂ ≅ Q.datum) :
    (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ Q E₂ e).datum = E₂ := rfl

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
/-- The `i`-th component projection of `PulledBackDatum.ofIso Q E₂ e` is the `i`-th component of
`e` followed by that of `Q`. -/
@[simp]
public lemma PulledBackDatum.ofIso_objMap {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (E₂ : DescentData f' hT' hX')
    (e : E₂ ≅ Q.datum) (i : ι') :
    (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ Q E₂ e).objMap i =
      (e.hom.hom i).left ≫ Q.objMap i := rfl

/-- The second projection of a gluing isomorphism read on literal fibre products. -/
private lemma gluingPullbackIso_hom_snd {ι₀ : Type*}
    {X₀ : ι₀ → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f₀ : ∀ i, X₀ i ⟶ T₀) (hT₀ : IsAlgebraicSpace B S hS T₀)
    (hX₀ : ∀ i, IsAlgebraicSpace B S hS (X₀ i)) (D₀ : DescentData f₀ hT₀ hX₀) (i j : ι₀) :
    (gluingPullbackIso f₀ hT₀ hX₀ D₀ i j).hom ≫
        pullback.snd (f₀ i) ((D₀.obj j).hom ≫ f₀ j) =
      (Over.prodLeftIsoPullback ((Over.map (f₀ i)).obj (D₀.obj i)) (Over.mk (f₀ j))).inv ≫
        (D₀.gluing i j).hom.left.left ≫
          (prod.snd : Over.mk (f₀ i) ⨯ (Over.map (f₀ j)).obj (D₀.obj j) ⟶ _).left := by
  have h := Over.prodLeftIsoPullback_hom_snd (Over.mk (f₀ i))
    ((Over.map (f₀ j)).obj (D₀.obj j))
  simp only [Over.mk_hom, Over.map_obj_hom] at h
  simp only [gluingPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Over.forget_map, Category.assoc, h]

include comm in
/-- The comparison of pairwise fibre products attached to a pair of indices: the component
projection of a pulled-back datum on the first factor and the morphism of families on the
second. -/
private def pairSourceMap {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i j : ι') :
    pullback ((Q.datum.obj i).hom ≫ f' i) (f' j) ⟶
      pullback ((D.obj (α i)).hom ≫ f (α i)) (f (α j)) :=
  pullback.lift
    (pullback.fst ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫ Q.objMap i)
    (pullback.snd ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫ gᵢ j) (by
      have hw := (Q.obj_isPullback i).w
      have hc : pullback.fst ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫
            ((Q.datum.obj i).hom ≫ f' i) =
          pullback.snd ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫ f' j := pullback.condition
      simp only [Category.assoc]
      rw [← reassoc_of% hw, comm i, reassoc_of% hc, comm j])

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
@[reassoc]
private lemma pairSourceMap_fst {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i j : ι') :
    pairSourceMap f f' hT hX hT' hX' α g gᵢ comm Q i j ≫
        pullback.fst ((D.obj (α i)).hom ≫ f (α i)) (f (α j)) =
      pullback.fst ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫ Q.objMap i :=
  pullback.lift_fst _ _ _

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
@[reassoc]
private lemma pairSourceMap_snd {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i j : ι') :
    pairSourceMap f f' hT hX hT' hX' α g gᵢ comm Q i j ≫
        pullback.snd ((D.obj (α i)).hom ≫ f (α i)) (f (α j)) =
      pullback.snd ((Q.datum.obj i).hom ≫ f' i) (f' j) ≫ gᵢ j :=
  pullback.lift_snd _ _ _

omit [Small.{u} ι] [B.AdmitsCoproductIndex ι] [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
/-- **The gluing isomorphism of a pulled-back datum is the base change of the original one.**
Read on literal fibre products: moving a point of the `i`-th component to the `j`-th component
and then projecting onto the original datum is projecting first and then moving. -/
private lemma gluingPullback_snd {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i j : ι') :
    (gluingPullbackIso f' hT' hX' Q.datum i j).hom ≫
        pullback.snd (f' i) ((Q.datum.obj j).hom ≫ f' j) ≫ Q.objMap j =
      pairSourceMap f f' hT hX hT' hX' α g gᵢ comm Q i j ≫
        (gluingPullbackIso f hT hX D (α i) (α j)).hom ≫
          pullback.snd (f (α i)) ((D.obj (α j)).hom ≫ f (α j)) := by
  have hkey : (Over.prodLeftIsoPullback ((Over.map (f' i)).obj (Q.datum.obj i))
        (Over.mk (f' j))).inv ≫ Q.gluingSourceMap i j =
      pairSourceMap f f' hT hX hT' hX' α g gᵢ comm Q i j ≫
        (Over.prodLeftIsoPullback ((Over.map (f (α i))).obj (D.obj (α i)))
          (Over.mk (f (α j)))).inv := by
    refine Over.prod_left_ext _ _ ?_ ?_
    · simp only [Category.assoc, Q.gluingSource_fst, Over.prodLeftIsoPullback_inv_fst,
        Over.prodLeftIsoPullback_inv_fst_assoc, Over.mk_hom, Over.map_obj_hom,
        pairSourceMap_fst]
    · simp only [Category.assoc, Q.gluingSource_snd, Over.prodLeftIsoPullback_inv_snd,
        Over.prodLeftIsoPullback_inv_snd_assoc, Over.mk_hom, Over.map_obj_hom,
        pairSourceMap_snd]
  have hq := Q.gluing_comm i j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hq
  have htgt := Q.gluingTarget_snd i j
  rw [reassoc_of% gluingPullbackIso_hom_snd f' hT' hX' Q.datum i j,
    gluingPullbackIso_hom_snd f hT hX D (α i) (α j), ← htgt,
    ← reassoc_of% hq, reassoc_of% hkey]

section Comparison

variable (E : FullFamilyCoproductEquivalence.{u, v, w} f hT hX Ycop)
  (E' : FullFamilyCoproductEquivalence.{u, v', w} f' hT' hX' Y'cop)

/-- The comparison of the coproduct of the components of a pulled-back datum with the
coproduct of the components of the original datum, read through the equivalences of
Tag 0ADK. -/
private def coproductComponent {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).left ⟶
      ((E.equivalence.functor.obj D).obj PUnit.unit).left :=
  (E'.objIso Q.datum).hom.left ≫
    (fullTotalCoproduct f' hT' hX' Q.datum).desc (fullTotalCoproduct f hT hX D).sheaf
      (fun i ↦ Q.objMap i ≫ ((fullTotalCoproduct f hT hX D).ι (α i)).hom) ≫
    (E.objIso D).inv.left

/-- The underlying map of the inverse of a comparison isomorphism of objects over a
coproduct cancels the underlying map of the isomorphism. -/
private lemma objIso_inv_hom_left {D : DescentData f hT hX} :
    (E.objIso D).inv.left ≫ (E.objIso D).hom.left = 𝟙 _ := by
  have h := congrArg Over.Hom.left (E.objIso D).inv_hom_id
  simp only [Over.comp_left, Over.id_left] at h
  exact h

/-- The underlying map of a comparison isomorphism of objects over a coproduct cancels the
underlying map of its inverse. -/
private lemma objIso_hom_inv_left {D : DescentData f hT hX} :
    (E.objIso D).hom.left ≫ (E.objIso D).inv.left = 𝟙 _ := by
  have h := congrArg Over.Hom.left (E.objIso D).hom_inv_id
  simp only [Over.comp_left, Over.id_left] at h
  exact h

/-- The comparison restricts on each summand to the component projection followed by the
inclusion of the corresponding summand. -/
private lemma ι_coproductComponent {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i : ι') :
    ((fullTotalCoproduct f' hT' hX' Q.datum).ι i).hom ≫
        (E'.objIso Q.datum).inv.left ≫
        coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q =
      Q.objMap i ≫ ((fullTotalCoproduct f hT hX D).ι (α i)).hom ≫
        (E.objIso D).inv.left := by
  simp only [coproductComponent]
  rw [← Category.assoc ((E'.objIso Q.datum).inv.left),
    objIso_inv_hom_left f' hT' hX' Y'cop E', Category.id_comp, ← Category.assoc,
    AlgebraicSheafCoproduct.ι_desc, Category.assoc]

/-- **The coproduct of the components of a pulled-back datum is the base change of the
coproduct of the components of the original datum.** -/
private lemma coproductComponent_isPullback {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    IsPullback ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom
      (coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)
      (coproductMap hX hX' α gᵢ Ycop Y'cop)
      ((E.equivalence.functor.obj D).obj PUnit.unit).hom := by
  have hpb := isPullback_totalCoproduct f f' hT hX hT' hX' α gᵢ Ycop Y'cop D Q.datum
    Q.objMap Q.obj_isPullback
  have h1 : IsIso ((E'.objIso Q.datum).hom.left) :=
    ((Over.forget Y'cop.sheaf.obj).mapIso (E'.objIso Q.datum)).isIso_hom
  have h2 : IsIso ((E.objIso D).inv.left) :=
    ((Over.forget Ycop.sheaf.obj).mapIso (E.objIso D).symm).isIso_hom
  have s1 : IsPullback ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom
      ((E'.objIso Q.datum).hom.left) (𝟙 Y'cop.sheaf.obj)
      ((fullTotalCoproduct f' hT' hX' Q.datum).map Y'cop
        (fun i ↦ (Q.datum.obj i).hom)) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    simpa using (Over.w (E'.objIso Q.datum).hom).symm
  have s2 : IsPullback
      ((fullTotalCoproduct f hT hX D).map Ycop (fun j ↦ (D.obj j).hom))
      ((E.objIso D).inv.left) (𝟙 Ycop.sheaf.obj)
      ((E.equivalence.functor.obj D).obj PUnit.unit).hom := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    simp
  simpa [coproductComponent, Category.assoc] using (s1.paste_vert hpb.flip).paste_vert s2

include comm in
/-- The morphism of the bases of the two squares of coproducts, as a map of spaces over the
target of the first family. -/
private abbrev coproductBase :=
  overStructureBase (Ycop.desc (spaceSheaf T hT) f) (Y'cop.desc (spaceSheaf T' hT') f') g
    (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)

include comm in
/-- The projection onto the coproduct of the components of the original datum, as a map of
spaces over the target of the first family. -/
private abbrev coproductProjection {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :=
  overStructureProjection (Ycop.desc (spaceSheaf T hT) f)
    (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    ((E.equivalence.functor.obj D).obj PUnit.unit)
    ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit)
    (coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)
    (coproductComponent_isPullback f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)

include comm in
/-- The pullback square of coproducts, as a base-change square for the structure morphisms. -/
private abbrev coproductSquare {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (_ : PUnit.{w + 1}) :=
  overBaseChangeSquare (Ycop.desc (spaceSheaf T hT) f)
    (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    ((E.equivalence.functor.obj D).obj PUnit.unit)
    ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit)
    (coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)
    (coproductComponent_isPullback f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)


include comm in
/-- The comparison of the sources of the two gluing isomorphisms of coproducts, on literal
fibre products. -/
private def coproductSourceMap {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    pullback (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
        Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ⟶
      pullback (((E.equivalence.functor.obj D).obj PUnit.unit).hom ≫
        Ycop.desc (spaceSheaf T hT) f) (Ycop.desc (spaceSheaf T hT) f) :=
  pullback.lift
    (pullback.fst (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
        Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
      coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q)
    (pullback.snd (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
        Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
      coproductMap hX hX' α gᵢ Ycop Y'cop) (by
      have hw := (coproductComponent_isPullback f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q).w
      have hc : pullback.fst (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
              Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
            (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
              Y'cop.desc (spaceSheaf T' hT') f') =
          pullback.snd (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
              Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
            Y'cop.desc (spaceSheaf T' hT') f' := pullback.condition
      simp only [Category.assoc]
      rw [← reassoc_of% hw, coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop,
        reassoc_of% hc])

include comm in
@[reassoc]
private lemma coproductSourceMap_fst {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
        pullback.fst (((E.equivalence.functor.obj D).obj PUnit.unit).hom ≫
          Ycop.desc (spaceSheaf T hT) f) (Ycop.desc (spaceSheaf T hT) f) =
      pullback.fst (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
          Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
        coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q :=
  pullback.lift_fst _ _ _

include comm in
@[reassoc]
private lemma coproductSourceMap_snd {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
        pullback.snd (((E.equivalence.functor.obj D).obj PUnit.unit).hom ≫
          Ycop.desc (spaceSheaf T hT) f) (Ycop.desc (spaceSheaf T hT) f) =
      pullback.snd (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
          Y'cop.desc (spaceSheaf T' hT') f') (Y'cop.desc (spaceSheaf T' hT') f') ≫
        coproductMap hX hX' α gᵢ Ycop Y'cop :=
  pullback.lift_snd _ _ _

include comm in
/-- The source comparison of the coproducts restricts, on each pair of summands, to the
pairwise comparison followed by the inclusion of that pair. -/
private lemma sourceMap_coproductSourceMap {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) (i j : ι') :
    E'.sourceMap Q.datum i j ≫
        coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q =
      pairSourceMap f f' hT hX hT' hX' α g gᵢ comm Q i j ≫ E.sourceMap D (α i) (α j) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, coproductSourceMap_fst, reassoc_of% (E'.sourceMap_fst Q.datum i j),
      ι_coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q i, Category.assoc,
      E.sourceMap_fst D (α i) (α j), pairSourceMap_fst_assoc]
  · rw [Category.assoc, coproductSourceMap_snd, reassoc_of% (E'.sourceMap_snd Q.datum i j),
      ι_coproductMap hX hX' α gᵢ Ycop Y'cop j, Category.assoc,
      E.sourceMap_snd D (α i) (α j), pairSourceMap_snd_assoc]

include comm in
/-- The source comparison of the coproducts, read through the identification of the pairwise
product in the over-category with the literal fibre product. -/
private lemma prodLift_coproductSourceMap {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    (Over.prodLeftIsoPullback
        ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).obj
          ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
        (Over.mk (Y'cop.desc (spaceSheaf T' hT') f'))).inv ≫
      (prod.lift
        ((Over.map g).map (prod.fst :
            (Over.map (Y'cop.desc (spaceSheaf T' hT') f')).obj
                ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit) ⨯
              Over.mk (Y'cop.desc (spaceSheaf T' hT') f') ⟶ _) ≫
          coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
        ((Over.map g).map prod.snd ≫
          coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)).left =
    coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
      (Over.prodLeftIsoPullback
        ((Over.map (Ycop.desc (spaceSheaf T hT) f)).obj
          ((E.equivalence.functor.obj D).obj PUnit.unit))
        (Over.mk (Ycop.desc (spaceSheaf T hT) f))).inv := by
  refine Over.prod_left_ext _ _ ?_ ?_
  · rw [Category.assoc, ← Over.comp_left, prod.lift_fst, Over.comp_left, Over.map_map_left,
      overStructureProjection_left, Over.prodLeftIsoPullback_inv_fst_assoc, Category.assoc,
      Over.prodLeftIsoPullback_inv_fst]
    simp only [Over.mk_hom, Over.map_obj_hom]
    rw [coproductSourceMap_fst]
  · rw [Category.assoc, ← Over.comp_left, prod.lift_snd, Over.comp_left, Over.map_map_left,
      overStructureBase_left, Over.prodLeftIsoPullback_inv_snd_assoc, Category.assoc,
      Over.prodLeftIsoPullback_inv_snd]
    simp only [Over.mk_hom, Over.map_obj_hom]
    rw [coproductSourceMap_snd]

include comm in
/-- **The gluing isomorphism of the coproduct of a pulled-back datum is the base change of the
gluing isomorphism of the coproduct of the original datum.** This is checked on each pair of
summands, which suffices because the pairwise fibre products of the summands jointly cover the
fibre product of the coproducts. -/
private lemma coproduct_gluingPullback_snd {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    (gluingPullbackIso (fun _ : PUnit.{w + 1} ↦ Y'cop.desc (spaceSheaf T' hT') f') hT'
          (fun _ ↦ Y'cop.isAlgebraicSpace) (E'.equivalence.functor.obj Q.datum)
          PUnit.unit PUnit.unit).hom ≫
        pullback.snd (Y'cop.desc (spaceSheaf T' hT') f')
            (((E'.equivalence.functor.obj Q.datum).obj PUnit.unit).hom ≫
              Y'cop.desc (spaceSheaf T' hT') f') ≫
          coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q =
      coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
        (gluingPullbackIso (fun _ : PUnit.{w + 1} ↦ Ycop.desc (spaceSheaf T hT) f) hT
            (fun _ ↦ Ycop.isAlgebraicSpace) (E.equivalence.functor.obj D)
            PUnit.unit PUnit.unit).hom ≫
          pullback.snd (Ycop.desc (spaceSheaf T hT) f)
            (((E.equivalence.functor.obj D).obj PUnit.unit).hom ≫
              Ycop.desc (spaceSheaf T hT) f) := by
  refine E'.sourceMap_jointly_epi Q.datum
    ((E.equivalence.functor.obj D).obj_isAlgebraicSpace PUnit.unit).isSheaf (fun i j ↦ ?_)
  rw [reassoc_of% (E'.gluing Q.datum i j), reassoc_of% (E'.targetMap_snd Q.datum i j),
    ι_coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q j,
    reassoc_of% (gluingPullback_snd f f' hT hX hT' hX' α g gᵢ comm Q i j),
    reassoc_of% (sourceMap_coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
      E E' Q i j),
    reassoc_of% (E.gluing D (α i) (α j)), E.targetMap_snd D (α i) (α j)]

include comm in
/-- **The move operation of the coproduct of a pulled-back datum is the base change of the
move operation of the coproduct of the original datum.** -/
private lemma coproduct_move {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) {Z : Over T'}
    (v : Z ⟶ (Over.map (Y'cop.desc (spaceSheaf T' hT') f')).obj
      ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
    (y : Z ⟶ Over.mk (Y'cop.desc (spaceSheaf T' hT') f')) :
    (Over.map g).map ((E'.equivalence.functor.obj Q.datum).transport.move v y) ≫
        coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q =
      (E.equivalence.functor.obj D).transport.move (i := PUnit.unit) (j := PUnit.unit)
        ((Over.map g).map v ≫
          coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
        ((Over.map g).map y ≫
          coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop) := by
  refine FamilyTransport.move_baseChange (i := PUnit.unit) (j := PUnit.unit)
    (q := fun _ ↦ coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
    (r := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    (E.equivalence.functor.obj D).transport
    (E'.equivalence.functor.obj Q.datum).transport (fun ii jj ↦ ?_) v y
  cases ii
  cases jj
  simp only [DescentData.transport_gluing]
  apply prod.hom_ext
  · have hsq := (coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q
      PUnit.unit).square
    simp only [Category.assoc, prod.lift_fst, DescentData.gluing_hom_fst, prod.lift_fst_assoc]
    rw [hsq, ← Category.assoc, ← Functor.map_comp,
      DescentData.gluing_hom_fst, Functor.map_comp, Category.assoc]
  · simp only [Category.assoc, prod.lift_snd]
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.map_map_left, overStructureProjection_left]
    refine (cancel_epi (Over.prodLeftIsoPullback
      ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).obj
        ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
      (Over.mk (Y'cop.desc (spaceSheaf T' hT') f'))).inv).mp ?_
    simp only
    rw [← reassoc_of% (gluingPullbackIso_hom_snd
        (fun _ : PUnit.{w + 1} ↦ Y'cop.desc (spaceSheaf T' hT') f') hT'
        (fun _ ↦ Y'cop.isAlgebraicSpace) (E'.equivalence.functor.obj Q.datum)
        PUnit.unit PUnit.unit),
      reassoc_of% (prodLift_coproductSourceMap f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E E' Q),
      ← gluingPullbackIso_hom_snd
        (fun _ : PUnit.{w + 1} ↦ Ycop.desc (spaceSheaf T hT) f) hT
        (fun _ ↦ Ycop.isAlgebraicSpace) (E.equivalence.functor.obj D)
        PUnit.unit PUnit.unit]
    exact coproduct_gluingPullback_snd f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q

/-- A map of the underlying spaces over the coproduct commuting with the move operations is a
morphism of the corresponding descent data for the single coproduct morphism. -/
private def homOfMoveCoproduct {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a₀ : Y₀ ⟶ X₀}
    {hX₀ : IsAlgebraicSpace B S hS X₀} {hY₀ : IsAlgebraicSpace B S hS Y₀}
    (D₀ E₀ : DescentData (fun _ : PUnit.{w + 1} ↦ a₀) hX₀ (fun _ ↦ hY₀))
    (m : (Over.map a₀).obj (D₀.obj PUnit.unit) ⟶ (Over.map a₀).obj (E₀.obj PUnit.unit))
    (hm : m ≫ structureMap a₀ (E₀.obj PUnit.unit) = structureMap a₀ (D₀.obj PUnit.unit))
    (ht : ∀ {Z : Over X₀} (v : Z ⟶ (Over.map a₀).obj (D₀.obj PUnit.unit))
      (y : Z ⟶ Over.mk a₀), D₀.transport.move v y ≫ m = E₀.transport.move (v ≫ m) y) :
    D₀ ⟶ E₀ := by
  have hml : m.left ≫ (E₀.obj PUnit.unit).hom = (D₀.obj PUnit.unit).hom := by
    simpa only [Over.comp_left, Over.homMk_left] using congrArg Over.Hom.left hm
  refine DescentData.homOfMove (fun _ ↦ Over.homMk m.left hml) ?_
  intro i j Z v y
  have hm' : (Over.map a₀).map
      (Over.homMk m.left hml : D₀.obj PUnit.unit ⟶ E₀.obj PUnit.unit) = m := by
    apply Over.OverMorphism.ext
    rfl
  rw [hm']
  exact ht v y

/-- The inverse comparison isomorphisms of Tag 0ADK are natural in the descent datum. -/
private lemma objIso_inv_naturality {D D₂ : DescentData f hT hX} (φ : D ⟶ D₂) :
    (E.objIso D).inv.left ≫ ((E.equivalence.functor.map φ).hom PUnit.unit).left =
      (fullTotalCoproduct f hT hX D).map (fullTotalCoproduct f hT hX D₂)
        (fun j ↦ (φ.hom j).left) ≫ (E.objIso D₂).inv.left := by
  have h := E.map φ
  have h2 : (E.objIso D).inv.left ≫ (E.objIso D).hom.left ≫
        (fullTotalCoproduct f hT hX D).map (fullTotalCoproduct f hT hX D₂)
          (fun j ↦ (φ.hom j).left) ≫ (E.objIso D₂).inv.left =
      (fullTotalCoproduct f hT hX D).map (fullTotalCoproduct f hT hX D₂)
        (fun j ↦ (φ.hom j).left) ≫ (E.objIso D₂).inv.left := by
    rw [← Category.assoc, objIso_inv_hom_left f hT hX Ycop E, Category.id_comp]
  rw [← h2, reassoc_of% h, objIso_hom_inv_left f hT hX Ycop E, Category.comp_id]

/-- The comparison of coproducts is natural in the descent datum: on each summand it is the
component projection, and those are natural. -/
private lemma coproductComponent_naturality {D D₂ : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q₂ : PulledBackDatum f f' hT hX hT' hX' α gᵢ D₂) (φ : D ⟶ D₂) (ψ : Q.datum ⟶ Q₂.datum)
    (hψ : ∀ i, (ψ.hom i).left ≫ Q₂.objMap i = Q.objMap i ≫ (φ.hom (α i)).left) :
    ((E'.equivalence.functor.map ψ).hom PUnit.unit).left ≫
        coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q₂ =
      coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q ≫
        ((E.equivalence.functor.map φ).hom PUnit.unit).left := by
  have : IsIso ((E'.objIso Q.datum).inv.left) :=
    ((Over.forget Y'cop.sheaf.obj).mapIso (E'.objIso Q.datum).symm).isIso_hom
  refine (cancel_epi (E'.objIso Q.datum).inv.left).mp ?_
  refine (fullTotalCoproduct f' hT' hX' Q.datum).desc_ext
    (spaceSheaf ((E.equivalence.functor.obj D₂).obj PUnit.unit).left
      ((E.equivalence.functor.obj D₂).obj_isAlgebraicSpace PUnit.unit)) (fun i ↦ ?_)
  have h1 := AlgebraicSheafCoproduct.ι_map (fullTotalCoproduct f' hT' hX' Q.datum)
    (fullTotalCoproduct f' hT' hX' Q₂.datum) (fun k ↦ (ψ.hom k).left) i
  have h2 := AlgebraicSheafCoproduct.ι_map (fullTotalCoproduct f hT hX D)
    (fullTotalCoproduct f hT hX D₂) (fun k ↦ (φ.hom k).left) (α i)
  rw [reassoc_of% (objIso_inv_naturality f' hT' hX' Y'cop E' ψ),
    reassoc_of% (ι_coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q i),
    objIso_inv_naturality f hT hX Ycop E φ,
    reassoc_of% h1,
    ι_coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q₂ i,
    reassoc_of% h2, ← reassoc_of% (hψ i)]

include comm in
/-- The projection onto the coproduct of the components of the original datum is natural in
the descent datum. -/
private lemma coproductProjection_naturality {D D₂ : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q₂ : PulledBackDatum f f' hT hX hT' hX' α gᵢ D₂) (φ : D ⟶ D₂) (ψ : Q.datum ⟶ Q₂.datum)
    (hψ : ∀ i, (ψ.hom i).left ≫ Q₂.objMap i = Q.objMap i ≫ (φ.hom (α i)).left) :
    (Over.map g).map ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).map
          ((E'.equivalence.functor.map ψ).hom PUnit.unit)) ≫
        coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q₂ =
      coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
        (Over.map (Ycop.desc (spaceSheaf T hT) f)).map
          ((E.equivalence.functor.map φ).hom PUnit.unit) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.map_map_left, overStructureProjection_left]
  exact coproductComponent_naturality f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q Q₂ φ ψ hψ

include comm in
/-- The pullback functor of Tag 0ADL for the square of coproducts induced by the morphism of
families. -/
private abbrev coproductPullbackFunctor :=
  pullbackDescentDataFunctor.{u, w, w} (Ycop.desc (spaceSheaf T hT) f)
    (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop) hT hT'
    Ycop.isAlgebraicSpace Y'cop.isAlgebraicSpace

include comm in
/-- The chosen comparison of the value of the Tag 0ADL pullback functor with the ordinary
pullback of the coproduct datum. -/
private abbrev coproductPullbackIso (D : DescentData f hT hX) :=
  Classical.choose (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
    Ycop Y'cop).property (E.equivalence.functor.obj D)

include comm in
/-- The projection of the Tag 0ADL pullback onto the coproduct datum, as a map of spaces over
the target of the first family. -/
private abbrev coproductPullbackProjection (D : DescentData f hT hX) :=
  overStructureProjection (Ycop.desc (spaceSheaf T hT) f)
    (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    ((E.equivalence.functor.obj D).obj PUnit.unit)
    (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
      Y'cop).val.obj (E.equivalence.functor.obj D)).obj PUnit.unit)
    ((coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D).hom.left ≫
      pullback.fst ((E.equivalence.functor.obj D).obj PUnit.unit).hom
        (coproductMap hX hX' α gᵢ Ycop Y'cop))
    (isPullback_of_overPullbackIso (coproductMap hX hX' α gᵢ Ycop Y'cop)
      ((E.equivalence.functor.obj D).obj PUnit.unit) _
      (coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E D))

include comm in
/-- The chosen pullback square of coproducts, as a base-change square. -/
private abbrev coproductPullbackSquare (D : DescentData f hT hX) (_ : PUnit.{w + 1}) :=
  overBaseChangeSquare (Ycop.desc (spaceSheaf T hT) f)
    (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
    (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    ((E.equivalence.functor.obj D).obj PUnit.unit)
    (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
      Y'cop).val.obj (E.equivalence.functor.obj D)).obj PUnit.unit)
    ((coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D).hom.left ≫
      pullback.fst ((E.equivalence.functor.obj D).obj PUnit.unit).hom
        (coproductMap hX hX' α gᵢ Ycop Y'cop))
    (isPullback_of_overPullbackIso (coproductMap hX hX' α gᵢ Ycop Y'cop)
      ((E.equivalence.functor.obj D).obj PUnit.unit) _
      (coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E D))

omit [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
include comm in
/-- The move operation of the Tag 0ADL pullback is the base change of the move operation of
the coproduct datum. -/
private lemma coproductPullback_move (D : DescentData f hT hX) {Z : Over T'}
    (v : Z ⟶ (Over.map (Y'cop.desc (spaceSheaf T' hT') f')).obj
      (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop).val.obj (E.equivalence.functor.obj D)).obj PUnit.unit))
    (y : Z ⟶ Over.mk (Y'cop.desc (spaceSheaf T' hT') f')) :
    (Over.map g).map
          (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
            Y'cop).val.obj (E.equivalence.functor.obj D)).transport.move v y) ≫
        coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E D =
      (E.equivalence.functor.obj D).transport.move (i := PUnit.unit) (j := PUnit.unit)
        ((Over.map g).map v ≫
          coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
            Y'cop E D)
        ((Over.map g).map y ≫
          coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop) := by
  obtain ⟨q, r, hq, hr, hg⟩ := (Classical.choose_spec
    (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
      Y'cop).property).2 (E.equivalence.functor.obj D)
  have eq : q = coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
      Ycop Y'cop E D := Over.OverMorphism.ext hq
  have er : r = coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop :=
    Over.OverMorphism.ext hr
  subst q r
  refine FamilyTransport.move_baseChange (i := PUnit.unit) (j := PUnit.unit)
    (q := fun _ ↦ coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
      Ycop Y'cop E D)
    (r := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
    (E.equivalence.functor.obj D).transport
    ((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
      Y'cop).val.obj (E.equivalence.functor.obj D)).transport (fun ii jj ↦ ?_) v y
  cases ii
  cases jj
  simp only [DescentData.transport_gluing]
  exact hg

omit [Small.{u} ι'] [B.AdmitsCoproductIndex ι'] in
include comm in
/-- The chosen projection of the Tag 0ADL pullback is natural in the descent datum. -/
private lemma coproductPullbackProjection_naturality {D D₂ : DescentData f hT hX}
    (φ : D ⟶ D₂) :
    (Over.map g).map ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).map
          (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
            Y'cop).val.map (E.equivalence.functor.map φ)).hom PUnit.unit)) ≫
        coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E D₂ =
      coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E D ≫
        (Over.map (Ycop.desc (spaceSheaf T hT) f)).map
          ((E.equivalence.functor.map φ).hom PUnit.unit) := by
  have hn := (Classical.choose_spec
    (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
      Y'cop).property).1 (E.equivalence.functor.map φ)
  have he := congrArg (fun k ↦ k.left ≫ pullback.fst
    ((E.equivalence.functor.obj D₂).obj PUnit.unit).hom
    (coproductMap hX hX' α gᵢ Ycop Y'cop)) hn
  apply Over.OverMorphism.ext
  simpa [Over.pullback_map_left, Over.comp_left, Over.map_map_left, Over.homMk_left,
    pullback.lift_fst] using he

include comm in
/-- The comparison morphism from the coproduct of a pulled-back datum to the Tag 0ADL
pullback of the coproduct datum. -/
private def comparisonHom {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    E'.equivalence.functor.obj Q.datum ⟶
      (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop).val.obj (E.equivalence.functor.obj D) :=
  homOfMoveCoproduct _ _
    ((coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E D
        PUnit.unit).compare
      (E.equivalence.functor.obj D).transport
      (structureMap (Y'cop.desc (spaceSheaf T' hT') f')
        ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
      (coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q))
    (BaseChangeSquare.compare_p _ _ _ _)
    (fun v y ↦ BaseChangeSquare.compare_move
      (R := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
      (R₀ := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
      (Q := fun _ ↦ coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
        Ycop Y'cop E D)
      (Q₀ := fun _ ↦ coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
      (coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E D
        PUnit.unit)
      (E.equivalence.functor.obj D).transport
      ((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop).val.obj (E.equivalence.functor.obj D)).transport
      (E'.equivalence.functor.obj Q.datum).transport
      (fun v y ↦ coproductPullback_move.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop E D v y)
      (fun v y ↦ coproduct_move f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q v y) v y)

include comm in
/-- The comparison morphism from the Tag 0ADL pullback of the coproduct datum to the
coproduct of a pulled-back datum. -/
private def comparisonInv {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop).val.obj (E.equivalence.functor.obj D) ⟶
      E'.equivalence.functor.obj Q.datum :=
  homOfMoveCoproduct _ _
    ((coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q PUnit.unit).compare
      (E.equivalence.functor.obj D).transport
      (structureMap (Y'cop.desc (spaceSheaf T' hT') f')
        (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop).val.obj (E.equivalence.functor.obj D)).obj PUnit.unit))
      (coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop E D))
    (BaseChangeSquare.compare_p _ _ _ _)
    (fun v y ↦ BaseChangeSquare.compare_move
      (R := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
      (R₀ := fun _ ↦ coproductBase f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop)
      (Q := fun _ ↦ coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
      (Q₀ := fun _ ↦ coproductPullbackProjection.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
        Ycop Y'cop E D)
      (coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q PUnit.unit)
      (E.equivalence.functor.obj D).transport
      (E'.equivalence.functor.obj Q.datum).transport
      ((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop).val.obj (E.equivalence.functor.obj D)).transport
      (fun v y ↦ coproduct_move f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q v y)
      (fun v y ↦ coproductPullback_move.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
        Y'cop E D v y) v y)

include comm in
/-- The two comparison morphisms are mutually inverse. -/
private lemma comparisonHom_comp {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    comparisonHom.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
      comparisonInv.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q = 𝟙 _ := by
  apply DescentData.Hom.ext
  funext i
  cases i
  apply Over.OverMorphism.ext
  have he := congrArg (fun k ↦ k.left)
    (BaseChangeSquare.compare_comp (i := PUnit.unit)
      (t := (E.equivalence.functor.obj D).transport)
      (L := coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D PUnit.unit)
      (L₀ := coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q PUnit.unit))
  simpa only [comparisonHom, comparisonInv, homOfMoveCoproduct, DescentData.homOfMove,
    DescentData.comp_hom, DescentData.id_hom, Over.homMk_left, Over.comp_left, Over.id_left,
    Over.map_obj_left] using he

include comm in
/-- The two comparison morphisms are mutually inverse, in the other order. -/
private lemma comparisonInv_comp {D : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D) :
    comparisonInv.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
      comparisonHom.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q = 𝟙 _ := by
  apply DescentData.Hom.ext
  funext i
  cases i
  apply Over.OverMorphism.ext
  have he := congrArg (fun k ↦ k.left)
    (BaseChangeSquare.compare_comp (i := PUnit.unit)
      (t := (E.equivalence.functor.obj D).transport)
      (L := coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q PUnit.unit)
      (L₀ := coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D PUnit.unit))
  simpa only [comparisonHom, comparisonInv, homOfMoveCoproduct, DescentData.homOfMove,
    DescentData.comp_hom, DescentData.id_hom, Over.homMk_left, Over.comp_left, Over.id_left,
    Over.map_obj_left] using he

include comm in
/-- The comparison morphism is natural in the descent datum. -/
private lemma comparisonHom_naturality {D D₂ : DescentData f hT hX}
    (Q : PulledBackDatum f f' hT hX hT' hX' α gᵢ D)
    (Q₂ : PulledBackDatum f f' hT hX hT' hX' α gᵢ D₂) (φ : D ⟶ D₂) (ψ : Q.datum ⟶ Q₂.datum)
    (hψ : ∀ i, (ψ.hom i).left ≫ Q₂.objMap i = Q.objMap i ≫ (φ.hom (α i)).left) :
    E'.equivalence.functor.map ψ ≫
        comparisonHom.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q₂ =
      comparisonHom.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q ≫
        (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop).val.map (E.equivalence.functor.map φ) := by
  apply DescentData.Hom.ext
  funext i
  cases i
  apply Over.OverMorphism.ext
  have he := congrArg (fun k ↦ k.left)
    (BaseChangeSquare.compare_naturality (i := PUnit.unit)
      (t := (E.equivalence.functor.obj D).transport)
      (u := (E.equivalence.functor.obj D₂).transport)
      (L := coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D PUnit.unit)
      (K := coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
        E D₂ PUnit.unit)
      (p₀ := structureMap (Y'cop.desc (spaceSheaf T' hT') f')
        ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
      (q₀ := coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
      (s₀ := structureMap (Y'cop.desc (spaceSheaf T' hT') f')
        ((E'.equivalence.functor.obj Q₂.datum).obj PUnit.unit))
      (qE₀ := coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q₂)
      (m := fun _ ↦ (Over.map (Ycop.desc (spaceSheaf T hT) f)).map
        ((E.equivalence.functor.map φ).hom PUnit.unit))
      ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).map
        ((E'.equivalence.functor.map ψ).hom PUnit.unit))
      ((Over.map (Y'cop.desc (spaceSheaf T' hT') f')).map
        (((coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop).val.map (E.equivalence.functor.map φ)).hom PUnit.unit))
      (structureMap_naturality (Y'cop.desc (spaceSheaf T' hT') f') _)
      (structureMap_naturality (Y'cop.desc (spaceSheaf T' hT') f') _)
      (coproductProjection_naturality f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E'
        Q Q₂ φ ψ hψ)
      (coproductPullbackProjection_naturality.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
        Ycop Y'cop E φ)
      (fun v y ↦ DescentData.move_naturality (E.equivalence.functor.map φ) v y))
  simpa only [comparisonHom, homOfMoveCoproduct, DescentData.homOfMove,
    DescentData.comp_hom, Over.homMk_left, Over.comp_left, Over.map_map_left] using he

include comm in
/-- The canonical isomorphism of functors asserted by Tag 0ADN part (4). -/
private def coproductComparisonIso (P : PullbackFunctor f f' hT hX hT' hX' α g gᵢ comm) :
    P.functor ⋙ E'.equivalence.functor ≅
      E.equivalence.functor ⋙ (coproductPullbackFunctor.{u, v, v', w} f f' hT hX hT' hX'
        α g gᵢ comm Ycop Y'cop).val :=
  NatIso.ofComponents
    (fun D ↦
      { hom := comparisonHom.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E'
          (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ
            (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm) (P.functor.obj D)
            (eqToIso (P.obj_eq D)))
        inv := comparisonInv.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E'
          (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ
            (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm) (P.functor.obj D)
            (eqToIso (P.obj_eq D)))
        hom_inv_id := comparisonHom_comp.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E E' _
        inv_hom_id := comparisonInv_comp.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E E' _ })
    (fun {D D₂} φ ↦
      comparisonHom_naturality.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E'
        (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ
          (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm) (P.functor.obj D)
          (eqToIso (P.obj_eq D)))
        (PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ
          (pullbackDatum f f' hT hX hT' hX' α gᵢ D₂ g comm) (P.functor.obj D₂)
          (eqToIso (P.obj_eq D₂)))
        φ (P.functor.map φ) (fun i ↦ by
          simp only [PulledBackDatum.ofIso_objMap, eqToIso.hom, Category.assoc]
          exact (P.map D D₂ φ i).symm))

include comm in
/-- The comparison isomorphism restricts on each summand of the coproduct to the projection of
the pulled-back component onto the original component. -/
private lemma coproductComparisonIso_spec
    (P : PullbackFunctor f f' hT hX hT' hX' α g gᵢ comm) (D : DescentData f hT hX) (i : ι') :
    ((fullTotalCoproduct f' hT' hX' (P.functor.obj D)).ι i).hom ≫
        (E'.objIso (P.functor.obj D)).inv.left ≫
        (((coproductComparisonIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
          E E' P).hom.app D).hom PUnit.unit).left ≫
        (coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
          E D).hom.left ≫
        pullback.fst ((E.equivalence.functor.obj D).obj PUnit.unit).hom
          (coproductMap hX hX' α gᵢ Ycop Y'cop) =
      ((eqToHom (P.obj_eq D)).hom i).left ≫
        (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm).objMap i ≫
        ((fullTotalCoproduct f hT hX D).ι (α i)).hom ≫ (E.objIso D).inv.left := by
  set Q := PulledBackDatum.ofIso f f' hT hX hT' hX' α gᵢ
    (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm) (P.functor.obj D)
    (eqToIso (P.obj_eq D))
  have hcq := BaseChangeSquare.compare_q
    (coproductPullbackSquare.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E D
      PUnit.unit)
    (E.equivalence.functor.obj D).transport
    (structureMap (Y'cop.desc (spaceSheaf T' hT') f')
      ((E'.equivalence.functor.obj Q.datum).obj PUnit.unit))
    (coproductProjection f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q)
  rw [← (coproductSquare f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop E E' Q PUnit.unit).square,
    (E.equivalence.functor.obj D).transport.move_self (i := PUnit.unit)] at hcq
  have hL : (((coproductComparisonIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop
          Y'cop E E' P).hom.app D).hom PUnit.unit).left ≫
        (coproductPullbackIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop
          E D).hom.left ≫
        pullback.fst ((E.equivalence.functor.obj D).obj PUnit.unit).hom
          (coproductMap hX hX' α gᵢ Ycop Y'cop) =
      coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q := by
    have h := congrArg Over.Hom.left hcq
    simp only [Over.comp_left, Over.map_map_left, overStructureProjection_left] at h
    exact h
  rw [hL]
  refine (ι_coproductComponent f f' hT hX hT' hX' α gᵢ Ycop Y'cop E E' Q i).trans ?_
  exact Category.assoc _ _ _

end Comparison

include comm in
/-- **Stacks Project, Tag 0ADN part (4).** Let `U = {X j → T}` and `U' = {X' i → T'}` be
families of morphisms of algebraic spaces over `S` with fixed target, and let
`α : I' → I`, `g : T' → T`, `gᵢ : X' i → X (α i)` be a morphism of families with fixed
target. The pullback functor on descent data along that morphism of families, Tag 0ADN
part (2), agrees — through the canonical equivalences of Tag 0ADK between descent data for a
family and descent data for the coproduct of its sources — with the pullback functor of
Tag 0ADL for the induced commutative square
`∐ X' i → ∐ X j`, `T' → T` of single morphisms.

The isomorphism is pinned on each summand: on the `i`-th summand of the coproduct of the
pulled-back components it is the projection of `X' i ×_{X (α i)} V (α i)` onto `V (α i)`,
followed by the inclusion of the `α i`-th summand of the coproduct of the original
components.

The index types are `u`-small and of cardinality below the cofinality of the site's size
cutoff, as is every countable index type. This is the same size condition that
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex` carries,
and it is what makes the coproducts exist at all. -/
@[stacks 0ADN "part (4), agreement with the pullback functors of 0ADL through 0ADK"]
public def pullbackFunctorCoproductComparison :
    let Ycop := sigmaAlgebraicSheafCoproduct X hX
    let Y'cop := sigmaAlgebraicSheafCoproduct X' hX'
    let E := familyCoproductEquivalenceOfAdmitsCoproductIndex.{u, v, w} f hT hX
    let E' := familyCoproductEquivalenceOfAdmitsCoproductIndex.{u, v', w} f' hT' hX'
    let P := pullbackFunctor f f' hT hX hT' hX' α g gᵢ comm
    let F := pullbackDescentDataFunctor.{u, w, w} (Ycop.desc (spaceSheaf T hT) f)
      (Y'cop.desc (spaceSheaf T' hT') f') g (coproductMap hX hX' α gᵢ Ycop Y'cop)
      (coproductMap_comm f f' hT hX hT' hX' α g gᵢ comm Ycop Y'cop) hT hT'
      Ycop.isAlgebraicSpace Y'cop.isAlgebraicSpace
    let αF := Classical.choose F.property
    { η : P.functor ⋙ E'.equivalence.functor ≅ E.equivalence.functor ⋙ F.val //
      ∀ (D : DescentData f hT hX) (i : ι'),
        ((fullTotalCoproduct f' hT' hX' (P.functor.obj D)).ι i).hom ≫
            (E'.objIso (P.functor.obj D)).inv.left ≫
            ((η.hom.app D).hom PUnit.unit).left ≫
            (αF (E.equivalence.functor.obj D)).hom.left ≫
            pullback.fst ((E.equivalence.functor.obj D).obj PUnit.unit).hom
              (coproductMap hX hX' α gᵢ Ycop Y'cop) =
          ((eqToHom (P.obj_eq D)).hom i).left ≫
            (pullbackDatum f f' hT hX hT' hX' α gᵢ D g comm).objMap i ≫
            ((fullTotalCoproduct f hT hX D).ι (α i)).hom ≫ (E.objIso D).inv.left } :=
  private_decl% (by
    exact ⟨coproductComparisonIso.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm _ _ _ _ _,
      fun D i ↦ coproductComparisonIso_spec.{u, v, v', w} f f' hT hX hT' hX' α g gᵢ comm
        _ _ _ _ _ D i⟩)

end AlgebraicGeometry.Space.Descent

end
