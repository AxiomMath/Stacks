module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# Morphisms into a base-changed étale chart

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces and `V` an étale chart of `Y`.
The base-changed chart `V ×_Y X` of `AlgebraicGeometry.Space.smallBaseChange` is a fibre product,
so a morphism into it from an étale chart `Z` of `X` is the same thing as a morphism
`Z ⟶ V` of the big fppf site compatible with the maps to `Y`.  This file packages that universal
property, and deduces that base change of charts carries the fibre products of
`AlgebraicGeometry.Space.SmallEtale.prodObj` to products.

## Main definitions

* `AlgebraicGeometry.Space.sbcProj`: the projection `V ×_Y X ⟶ V`, on objects of the big site.
* `AlgebraicGeometry.Space.sbcLift`: the morphism into `V ×_Y X` with a given projection.

## Main results

* `AlgebraicGeometry.Space.sbcLift_proj` and `AlgebraicGeometry.Space.sbc_hom_ext`: the universal
  property.
* `AlgebraicGeometry.Space.isLimitSmallBaseChangeOfIsLimit`: base change of charts preserves the
  binary products of the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- The projection of a base-changed chart to the original chart, on objects of the big site. -/
abbrev sbcProj (V : SmallEtale B S hS Y.1) :
    ((smallBaseChange B S hS f hf).obj V).obj.left ⟶ V.obj.left :=
  hf.snd V.obj.hom

/-- The projection of a base-changed chart commutes with the maps to `Y`. -/
theorem sbc_w (V : SmallEtale B S hS Y.1) :
    yoneda.map (sbcProj f hf V) ≫ V.obj.hom = ((smallBaseChange B S hS f hf).obj
        V).obj.hom ≫ f.hom :=
  (hf.w V.obj.hom).symm

/-- The morphism into a base-changed chart with a given projection. -/
def sbcLift {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} (a : Z.obj.left ⟶ V.obj.left)
    (h : yoneda.map a ≫ V.obj.hom = Z.obj.hom ≫ f.hom) : Z ⟶ (smallBaseChange B S hS f hf).obj V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hf.lift Z.obj.hom a h.symm) (hf.lift_fst _ _ _))

/-- The morphism `sbcLift f hf a h` composed with the projection is `a`. -/
@[simp]
theorem sbcLift_proj {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (a : Z.obj.left ⟶ V.obj.left) (h : yoneda.map a ≫ V.obj.hom = Z.obj.hom ≫ f.hom) :
    (sbcLift f hf a h).hom.left ≫ sbcProj f hf V = a :=
  hf.lift_snd _ _ _

/-- Morphisms into a base-changed chart agree if their projections to the original chart agree. -/
theorem sbc_hom_ext {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {t t' : Z ⟶ (smallBaseChange B S hS f hf).obj V}
    (h : t.hom.left ≫ sbcProj f hf V = t'.hom.left ≫ sbcProj f hf V) : t = t' := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hf.hom_ext ?_ h))
  exact (CostructuredArrow.w t.hom).trans (CostructuredArrow.w t'.hom).symm

/-- The base change of a morphism of charts commutes with the projections. -/
theorem smallBaseChange_map_proj {V V' : SmallEtale B S hS Y.1} (k : V ⟶ V') :
    ((smallBaseChange B S hS f hf).map k).hom.left ≫ sbcProj f hf V' =
      sbcProj f hf V ≫ k.hom.left :=
  smallBaseChange_map_snd B S hS f hf k

/-- The compatibility of a morphism into a base-changed chart with the maps to `Y`. -/
theorem sbc_comp_proj_w {Z : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (t : Z ⟶ (smallBaseChange B S hS f hf).obj V) :
    yoneda.map (t.hom.left ≫ sbcProj f hf V) ≫ V.obj.hom = Z.obj.hom ≫ f.hom :=
  by rw [Functor.map_comp, Category.assoc, sbc_w, ← Category.assoc, CostructuredArrow.w]

/-- The projection of a morphism into a base-changed chart followed by the base change of a
morphism of charts. -/
private theorem comp_map_sbcProj {Z : SmallEtale B S hS X.1} {V V' : SmallEtale B S hS Y.1}
    (t : Z ⟶ (smallBaseChange B S hS f hf).obj V) (k : V ⟶ V') :
    (t ≫ (smallBaseChange B S hS f hf).map k).hom.left ≫ sbcProj f hf V' =
      t.hom.left ≫ sbcProj f hf V ≫ k.hom.left := by
  rw [← smallBaseChange_map_proj, ← Category.assoc]
  rfl

section Prod

variable (A A' : SmallEtale B S hS Y.1)

/-- The base change of the first projection of `SmallEtale.prodObj` commutes with the projections
to the original charts. -/
theorem prodFst_proj :
    ((smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS Y.1 A A')).hom.left ≫
      sbcProj f hf A =
    sbcProj f hf (SmallEtale.prodObj B S hS Y.1 A A') ≫ A.property.rep.fst' A'.obj.hom :=
  smallBaseChange_map_proj f hf _

/-- The base change of the second projection of `SmallEtale.prodObj` commutes with the projections
to the original charts. -/
theorem prodSnd_proj :
    ((smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS Y.1 A A')).hom.left ≫
      sbcProj f hf A' =
    sbcProj f hf (SmallEtale.prodObj B S hS Y.1 A A') ≫ A.property.rep.snd A'.obj.hom :=
  smallBaseChange_map_proj f hf _

variable {A A'}

/-- Two morphisms into base-changed charts of `A` and `A'` have projections agreeing over `Y`. -/
theorem prodLift_cond {V : SmallEtale B S hS X.1} (h : V ⟶ (smallBaseChange B S hS f hf).obj A)
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj A') :
    yoneda.map (h.hom.left ≫ sbcProj f hf A) ≫ A.obj.hom =
      yoneda.map (h'.hom.left ≫ sbcProj f hf A') ≫ A'.obj.hom := by
  rw [sbc_comp_proj_w, sbc_comp_proj_w]

/-- The morphism into the base change of a product with two given components. -/
def prodLift {V : SmallEtale B S hS X.1} (h : V ⟶ (smallBaseChange B S hS f hf).obj A)
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj A') :
    V ⟶ (smallBaseChange B S hS f hf).obj (SmallEtale.prodObj B S hS Y.1 A A') :=
  sbcLift f hf (A.property.rep.lift' (h.hom.left ≫ sbcProj f hf A) (h'.hom.left ≫ sbcProj f hf A')
    (prodLift_cond f hf h h')) (by
      change yoneda.map _ ≫ yoneda.map (A.property.rep.snd A'.obj.hom) ≫ A'.obj.hom = _
      rw [← Functor.map_comp_assoc, Functor.relativelyRepresentable.lift'_snd, sbc_comp_proj_w])

/-- The projection of `prodLift f hf h h'` is the morphism into the fibre product determined by the
projections of `h` and `h'`. -/
theorem prodLift_proj {V : SmallEtale B S hS X.1} (h : V ⟶ (smallBaseChange B S hS f hf).obj A)
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj A') :
    (prodLift f hf h h').hom.left ≫ sbcProj f hf (SmallEtale.prodObj B S hS Y.1 A A') =
      A.property.rep.lift' (h.hom.left ≫ sbcProj f hf A) (h'.hom.left ≫ sbcProj f hf A')
        (prodLift_cond f hf h h') :=
  sbcLift_proj f hf _ _

/-- `prodLift f hf h h'` followed by the base change of the first projection is `h`. -/
theorem prodLift_fst {V : SmallEtale B S hS X.1} (h : V ⟶ (smallBaseChange B S hS f hf).obj A)
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj A') :
    prodLift f hf h h' ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS Y.1 A A') =
      h := by
  apply sbc_hom_ext
  rw [comp_map_sbcProj, ← Category.assoc, prodLift_proj]
  exact Functor.relativelyRepresentable.lift'_fst _ _ _ _

/-- `prodLift f hf h h'` followed by the base change of the second projection is `h'`. -/
theorem prodLift_snd {V : SmallEtale B S hS X.1} (h : V ⟶ (smallBaseChange B S hS f hf).obj A)
    (h' : V ⟶ (smallBaseChange B S hS f hf).obj A') :
    prodLift f hf h h' ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS Y.1 A A') =
      h' := by
  apply sbc_hom_ext
  rw [comp_map_sbcProj, ← Category.assoc, prodLift_proj]
  exact Functor.relativelyRepresentable.lift'_snd _ _ _ _

/-- Two morphisms into the base change of `SmallEtale.prodObj` agree if they agree after the base
changes of both projections. -/
theorem prod_hom_ext {V : SmallEtale B S hS X.1}
    {t t' : V ⟶ (smallBaseChange B S hS f hf).obj (SmallEtale.prodObj B S hS Y.1 A A')}
    (h₁ : t ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS Y.1 A A') =
      t' ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS Y.1 A A'))
    (h₂ : t ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS Y.1 A A') =
      t' ≫ (smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS Y.1 A A')) : t = t' := by
  apply sbc_hom_ext
  refine Functor.relativelyRepresentable.hom_ext' _ ?_ ?_
  · have := congrArg (fun r => r.hom.left ≫ sbcProj f hf A) h₁
    simp only [comp_map_sbcProj, ← Category.assoc] at this
    exact this
  · have := congrArg (fun r => r.hom.left ≫ sbcProj f hf A') h₂
    simp only [comp_map_sbcProj, ← Category.assoc] at this
    exact this

end Prod

/-- Base change of charts carries every binary product of the small étale site to a product. -/
def isLimitSmallBaseChangeOfIsLimit {A A' P : SmallEtale B S hS Y.1} {p₁ : P ⟶ A} {p₂ : P ⟶ A'}
    (hP : IsLimit (BinaryFan.mk p₁ p₂)) :
    IsLimit (BinaryFan.mk ((smallBaseChange B S hS f hf).map p₁)
      ((smallBaseChange B S hS f hf).map p₂)) :=
  let e : P ≅ SmallEtale.prodObj B S hS Y.1 A A' :=
    hP.conePointUniqueUpToIso (SmallEtale.prodIsLimit B S hS Y.1 A A')
  IsLimit.ofIsoLimit (BinaryFan.isLimitMk
    (fst := (smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS Y.1 A A'))
    (snd := (smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS Y.1 A A'))
    (fun s => prodLift f hf s.fst s.snd) (fun s => prodLift_fst f hf _ _)
    (fun s => prodLift_snd f hf _ _) (fun s m h₁ h₂ => prod_hom_ext f hf
      (h₁.trans (prodLift_fst f hf _ _).symm) (h₂.trans (prodLift_snd f hf _ _).symm)))
    (BinaryFan.ext ((smallBaseChange B S hS f hf).mapIso e).symm
      (by
        have h := hP.conePointUniqueUpToIso_inv_comp (SmallEtale.prodIsLimit B S hS Y.1 A A')
          ⟨WalkingPair.left⟩
        change _ = (smallBaseChange B S hS f hf).map e.inv ≫ (smallBaseChange B S hS f hf).map p₁
        rw [← Functor.map_comp]
        exact congrArg (smallBaseChange B S hS f hf).map h.symm)
      (by
        have h := hP.conePointUniqueUpToIso_inv_comp (SmallEtale.prodIsLimit B S hS Y.1 A A')
          ⟨WalkingPair.right⟩
        change _ = (smallBaseChange B S hS f hf).map e.inv ≫ (smallBaseChange B S hS f hf).map p₂
        rw [← Functor.map_comp]
        exact congrArg (smallBaseChange B S hS f hf).map h.symm))

/-! ### Covering the final object by points -/

/-- A family of étale charts is *jointly surjective on points*. -/
def PointsCover {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {K : Type*} (W : K → SmallEtale B S hS F) :
    Prop :=
  ∀ x : points B S hS F, ∃ k, x ∈ Set.range (pointsMap B S hS _ (W k).obj.hom)

/-- **A family of étale charts jointly surjective on points covers the final object.** -/
theorem coversTop_of_pointsCover {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {K : Type*}
    {W : K → SmallEtale B S hS F} (hW : PointsCover W) :
    (SmallEtale.topology B S hS F).CoversTop W := by
  intro V
  refine smallEtale_sieve_of_pointwise_covering B S hS F V _ (fun z => ?_)
  obtain ⟨y, rfl⟩ := surjective_pointsToScheme B S hS V.obj.left z
  obtain ⟨k, w, hw⟩ := hW (pointsMap B S hS _ V.obj.hom y)
  obtain ⟨q, hq, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (V.property.rep.isPullback (W k).obj.hom) y w hw.symm
  refine ⟨SmallEtale.prodObj B S hS F V (W k), SmallEtale.prodFst B S hS F V (W k),
    ⟨k, ⟨SmallEtale.prodSnd B S hS F V (W k)⟩⟩,
    pointsToScheme B S hS (SmallEtale.prodObj B S hS F V (W k)).obj.left q, ?_⟩
  have h1 := pointsToScheme_pointsMap_yoneda B S hS (V.property.rep.fst' (W k).obj.hom) q
  rw [Functor.relativelyRepresentable.map_fst', hq] at h1
  exact h1.symm

/-- **Base change of charts preserves joint surjectivity on points.** -/
theorem pointsCover_smallBaseChange {K : Type*} {W : K → SmallEtale B S hS Y.1}
    (hW : PointsCover W) : PointsCover (fun k => (smallBaseChange B S hS f hf).obj (W k)) := by
  intro x
  obtain ⟨k, w, hw⟩ := hW (pointsMap B S hS _ f.hom x)
  obtain ⟨q, hq, -⟩ := exists_point_of_isPullback_presheaf B S hS (hf.isPullback (W k).obj.hom)
    x w hw.symm
  exact ⟨k, q, hq⟩

end AlgebraicGeometry.Space
