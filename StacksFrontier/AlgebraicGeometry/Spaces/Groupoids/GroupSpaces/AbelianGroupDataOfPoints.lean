module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsFirstCohomologyClass

/-!
# The acting groups of a group algebraic space given by its points

Let `ℬ` be an algebraic space over `S` and let `G_ℬ = ℬ ×_S P` be the group algebraic space
over `ℬ` whose points over a scheme `T` over `ℬ` are the sections over `T` of a presheaf of
groups `F` on the big fppf site of `S`
(`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofPointsFunctor`). If the sections of `F` are
identified, naturally, with the sections of an abelian sheaf `A`, then the acting groups
`U ×_{b, ℬ} G_ℬ` of the objects of `G_ℬ/ℬ-Torsors` are identified with the restrictions `A|_U`,
compatibly with base change. This is the datum `AlgebraicGeometry.Space.AbelianGroupData` that
`AlgebraicGeometry.Space.SheafTorsors.h1Class` needs.

## Main definitions

* `AlgebraicGeometry.Space.pullbackAdjMulEquiv`: the points of the base change of a group object
  are the points of the group object, as groups.
* `AlgebraicGeometry.Space.abelianGroupDataOfPoints`: the datum `AbelianGroupData` for the group
  algebraic space given by its points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_AbelianGroupDataOfPoints
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_AbelianGroupDataOfPoints
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_AbelianGroupDataOfPoints.has_limit _

open Stacks.Cohomology.Torsors

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {ℬ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-- **The points of a base change of a group object are its points.** For `b : U ⟶ ℬ`, the
group of points over `Y` of the base change `U ×_{b, ℬ} G` is the group of points over the image
of `Y` of `G`. -/
def pullbackAdjMulEquiv {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ) (G : Grp (Over ℬ))
    (Y : Over (yoneda.obj U)) :
    ((Over.map b).obj Y ⟶ G.X) ≃* (Y ⟶ (sheafPullbackGroup G U b).X) where
  __ := (Over.mapPullbackAdj b).homEquiv Y G.X
  map_mul' f g :=
    letI : (Over.pullback b).Monoidal := Over.instBraidedPullback.toMonoidal
    (congrArg (fun t => (Over.mapPullbackAdj b).unit.app Y ≫ t)
      ((Over.pullback b).map_mul f g)).trans (MonObj.comp_mul _ _ _)

/-- The first component of the point of a base change attached to a point of `G`. -/
theorem pullbackAdjMulEquiv_left_fst {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
    (G : Grp (Over ℬ)) (Y : Over (yoneda.obj U)) (g : (Over.map b).obj Y ⟶ G.X) :
    (pullbackAdjMulEquiv b G Y g).left ≫ pullback.fst G.X.hom b = g.left := by
  change ((Over.mapPullbackAdj b).homEquiv Y G.X g).left ≫ pullback.fst G.X.hom b = g.left
  rw [Adjunction.homEquiv_unit]
  simp only [Over.pullback_obj_left, Functor.comp_obj, Over.mapPullbackAdj_unit_app,
    Over.comp_left, Over.map_obj_left, Over.map_obj_hom, Over.homMk_left, Over.pullback_map_left,
    Category.assoc]
  rw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.id_comp]

/-- The second component of the point of a base change attached to a point of `G`. -/
theorem pullbackAdjMulEquiv_left_snd {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
    (G : Grp (Over ℬ)) (Y : Over (yoneda.obj U)) (g : (Over.map b).obj Y ⟶ G.X) :
    (pullbackAdjMulEquiv b G Y g).left ≫ pullback.snd G.X.hom b = Y.hom := by
  change ((Over.mapPullbackAdj b).homEquiv Y G.X g).left ≫ pullback.snd G.X.hom b = Y.hom
  exact Over.w ((Over.mapPullbackAdj b).homEquiv Y G.X g)

/-- The naturality of `pullbackAdjMulEquiv` in the object over `U`. -/
theorem pullbackAdjMulEquiv_naturality {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
    (G : Grp (Over ℬ)) {Y Y' : Over (yoneda.obj U)} (k : Y' ⟶ Y)
    (g : (Over.map b).obj Y ⟶ G.X) :
    pullbackAdjMulEquiv b G Y' ((Over.map b).map k ≫ g) = k ≫ pullbackAdjMulEquiv b G Y g :=
  (Over.mapPullbackAdj b).homEquiv_naturality_left k g

variable (𝒞 S hS ℬ) (hℬ : IsAlgebraicSpace 𝒞 S hS ℬ) (F : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ GrpCat.{u})
  {a₀ : BigFppfOver 𝒞 S hS} (r : (F ⋙ forget GrpCat).RepresentableBy a₀)
  (A : Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})
  (ιA : ∀ T : BigFppfOver 𝒞 S hS, F.obj (op T) ≃* Multiplicative (A.obj.obj (op T)))
  (hιA : ∀ {T T' : BigFppfOver 𝒞 S hS} (f : T' ⟶ T) (x : F.obj (op T)),
    ιA T' (F.map f.op x) = Multiplicative.ofAdd (A.obj.map f.op (ιA T x).toAdd))

/-- The acting groups of the group algebraic space given by its points are sheaves. -/
theorem isSheaf_sheafPullbackGroup_ofPointsFunctor (U : BigFppfOver 𝒞 S hS)
    (b : yoneda.obj U ⟶ ℬ) :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS)
      (sheafPullbackGroup (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj
        U b).X.left :=
  Presheaf.isSheaf_pullback _ _ b
    (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).property.isSheaf
    (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf hℬ.isSheaf

/-- The identification of the points over `(W, a)` of the acting group with the sections of
`A` over `W`. -/
def pointsSliceMulEquiv {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ) (W : Over U) :
    Multiplicative (A.obj.obj (op W.left)) ≃*
      (sliceOver W ⟶ (sheafPullbackGroup (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj
        U b).X) :=
  (ιA W.left).symm.trans ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.left
    (yoneda.map W.hom ≫ b)).symm.trans (pullbackAdjMulEquiv b
      (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W)))

/-- `pointsSliceMulEquiv`, unfolded. -/
theorem pointsSliceMulEquiv_apply {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ) (W : Over U)
    (x : Multiplicative (A.obj.obj (op W.left))) :
    pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b W x =
      pullbackAdjMulEquiv b (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W)
        ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.left (yoneda.map W.hom ≫ b)).symm
          ((ιA W.left).symm x)) :=
  rfl

/-- The point of `G` underlying the point of the acting group attached to a section of `A`. -/
theorem pointsMulEquiv_symm_left_prodSnd {T : BigFppfOver 𝒞 S hS} (c : yoneda.obj T ⟶ ℬ)
    (y : F.obj (op T)) :
    ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F T c).symm y).left ≫
        (prod.snd : ℬ ⨯ (F ⋙ forget GrpCat) ⟶ F ⋙ forget GrpCat) =
      yonedaEquiv.symm y := by
  apply yonedaEquiv.injective
  rw [← GroupAlgebraicSpace.pointsMulEquiv_apply, MulEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The first component of the point of `G` attached to a section lies over its section of
`ℬ`. -/
theorem pointsMulEquiv_symm_left_prodFst {T : BigFppfOver 𝒞 S hS} (c : yoneda.obj T ⟶ ℬ)
    (y : F.obj (op T)) :
    ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F T c).symm y).left ≫
        (prod.fst : ℬ ⨯ (F ⋙ forget GrpCat) ⟶ ℬ) = c :=
  Over.w ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F T c).symm y)

include ιA hιA in
/-- **The datum `AbelianGroupData` for the group algebraic space given by its points.** -/
def abelianGroupDataOfPoints :
    AbelianGroupData (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj A
      (isSheaf_sheafPullbackGroup_ofPointsFunctor 𝒞 S hS ℬ hℬ F r) where
  equiv U b :=
    { equiv V := (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b V.unop).toEquiv.trans
        (sliceSectionEquiv _ V.unop)
      map_mul V g h :=
        (congrArg (sliceSectionEquiv _ V.unop)
          (map_mul (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b V.unop) g h)).trans
          (sliceSectionEquiv_mul (isSheaf_sheafPullbackGroup_ofPointsFunctor 𝒞 S hS ℬ hℬ F r U b)
            V.unop _ _)
      naturality {V W} f g := by
        change sliceSectionEquiv _ W.unop (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b W.unop
          (Multiplicative.ofAdd (A.obj.map f.unop.left.op (Multiplicative.toAdd g)))) =
          (sliceSection _).map f (sliceSectionEquiv _ V.unop
            (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b V.unop g))
        rw [sliceSectionEquiv_map]
        congr 1
        apply (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b W.unop).symm.injective
        rw [MulEquiv.symm_apply_apply]
        change _ = ιA W.unop.left (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.unop.left
          (yoneda.map W.unop.hom ≫ b) ((pullbackAdjMulEquiv b
            (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W.unop)).symm
            (sliceRestrict f.unop ≫ pullbackAdjMulEquiv b
              (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver V.unop)
              ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F V.unop.left
                (yoneda.map V.unop.hom ≫ b)).symm ((ιA V.unop.left).symm g)))))
        have e1 : (pullbackAdjMulEquiv b
            (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W.unop)).symm
            (sliceRestrict f.unop ≫ pullbackAdjMulEquiv b
              (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver V.unop)
              ((GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F V.unop.left
                (yoneda.map V.unop.hom ≫ b)).symm ((ιA V.unop.left).symm g))) =
            (Over.map b).map (sliceRestrict f.unop) ≫
              (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F V.unop.left
                (yoneda.map V.unop.hom ≫ b)).symm ((ιA V.unop.left).symm g) :=
          (MulEquiv.symm_apply_eq _).2 (pullbackAdjMulEquiv_naturality b
            (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj _ _).symm
        have hk : ((Over.map b).map (sliceRestrict f.unop) ≫
            (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F V.unop.left
              (yoneda.map V.unop.hom ≫ b)).symm ((ιA V.unop.left).symm g)).left ≫
              (prod.snd : ℬ ⨯ (F ⋙ forget GrpCat) ⟶ F ⋙ forget GrpCat) =
            yoneda.map f.unop.left ≫ yonedaEquiv.symm ((ιA V.unop.left).symm g) :=
          (Category.assoc _ _ _).trans (whisker_eq _
            (pointsMulEquiv_symm_left_prodSnd 𝒞 S hS ℬ F _ _))
        have e2 : GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.unop.left
            (yoneda.map W.unop.hom ≫ b) ((Over.map b).map (sliceRestrict f.unop) ≫
              (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F V.unop.left
                (yoneda.map V.unop.hom ≫ b)).symm ((ιA V.unop.left).symm g)) =
            F.map f.unop.left.op ((ιA V.unop.left).symm g) := by
          refine (GroupAlgebraicSpace.pointsMulEquiv_apply _ _ _ _ _ _ _ _).trans ?_
          rw [hk, yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
          rfl
        rw [e1, e2]
        refine ((hιA f.unop.left _).trans ?_).symm
        exact congrArg (fun y => Multiplicative.ofAdd (A.obj.map f.unop.left.op
          (Multiplicative.toAdd y))) ((ιA V.unop.left).apply_symm_apply g) }
  equiv_baseChange {U U' b b'} f hf W a ha x := by
    subst ha hf
    have key : (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA b' (Over.mk (W.hom ≫ f)) x).left =
        (pointsSliceMulEquiv 𝒞 S hS ℬ hℬ F r A ιA (yoneda.map f ≫ b') W x).left ≫
          pullbackGroupMap (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj f rfl := by
      set y' := (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.left
        (yoneda.map (W.hom ≫ f) ≫ b')).symm ((ιA W.left).symm x)
      set y := (GroupAlgebraicSpace.pointsMulEquiv 𝒞 S hS ℬ F W.left
        (yoneda.map W.hom ≫ yoneda.map f ≫ b')).symm ((ιA W.left).symm x)
      have hy : y'.left = y.left := by
        apply prod.hom_ext
        · refine (pointsMulEquiv_symm_left_prodFst 𝒞 S hS ℬ F _ _).trans
            (Eq.trans ?_ (pointsMulEquiv_symm_left_prodFst 𝒞 S hS ℬ F _ _).symm)
          exact (eq_whisker (yoneda.map_comp _ _) _).trans (Category.assoc _ _ _)
        · exact (pointsMulEquiv_symm_left_prodSnd 𝒞 S hS ℬ F _ _).trans
            (pointsMulEquiv_symm_left_prodSnd 𝒞 S hS ℬ F _ _).symm
      apply pullback.hom_ext
      · refine (pullbackAdjMulEquiv_left_fst b'
          (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj
          (sliceOver (Over.mk (W.hom ≫ f))) y').trans ?_
        refine hy.trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        refine Eq.trans ?_ (whisker_eq _ (pullback.lift_fst _ _ _)).symm
        refine Eq.trans ?_ (whisker_eq _ (Category.comp_id _)).symm
        exact (pullbackAdjMulEquiv_left_fst (yoneda.map f ≫ b')
          (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W) y).symm
      · refine (pullbackAdjMulEquiv_left_snd b'
          (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj
          (sliceOver (Over.mk (W.hom ≫ f))) y').trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        refine Eq.trans ?_ (whisker_eq _ (pullback.lift_snd _ _ _)).symm
        refine Eq.trans ?_ (Category.assoc _ _ _)
        refine Eq.trans ?_ (eq_whisker
          (pullbackAdjMulEquiv_left_snd (yoneda.map f ≫ b')
            (GroupAlgebraicSpace.ofPointsFunctor 𝒞 S hS ℬ hℬ F r).obj (sliceOver W) y) _).symm
        exact yoneda.map_comp _ _
    exact (congrArg yonedaEquiv key).trans (yonedaEquiv_comp _ _)

end AlgebraicGeometry.Space

end
