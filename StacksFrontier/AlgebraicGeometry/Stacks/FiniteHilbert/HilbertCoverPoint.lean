module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.AbsoluteOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal

/-!
# A degree-`d` cover of an object of the site is a point of `ℋ_d`

Let `B` be a big fppf site, `S` a scheme contained in it, `d` a natural number, and let
`c : W ⟶ U` be a morphism of objects of the big fppf site of `S` which is finite locally free of
degree `d`. The category `ℋ_d` of degree-`d` finite locally free covers
(`AlgebraicGeometry.Stack.finiteCoverCategory`) then receives a 1-morphism from the category
represented by `U`, namely the one sending an object `T ⟶ U` of the slice of the site at `U` to
the base change `W ×_U T ⟶ T` of `c`.

## Main definitions

* `AlgebraicGeometry.Stack.finiteCoverPointObj` and
  `AlgebraicGeometry.Stack.finiteCoverPointMap`: the base change of `c` along an object of the
  slice of the site at `U`, and along a morphism of that slice.
* `AlgebraicGeometry.Stack.finiteCoverPointFunctor`: the functor from the slice of the site at
  `U` to `ℋ_d` these two assemble into.
* `AlgebraicGeometry.Stack.finiteCoverPoint`: the same as a 1-morphism of categories over the
  site, from the category represented by `U` to `ℋ_d`.
* `AlgebraicGeometry.Stack.finiteCoverPointHom`: the same as a 1-morphism of the 2-category of
  categories fibred in groupoids over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Stack.isPullback_liftPullbackSnd`: the square cutting a fibre product of a
  fixed morphism down along a morphism of the base is cartesian.
* `AlgebraicGeometry.Stack.finiteCoverPointFunctor_obj_q` and
  `AlgebraicGeometry.Stack.finiteCoverPointFunctor_map_f`: the cover attached to `T ⟶ U` is the
  second projection of the fibre product of `c` with it, and the base component of the image of a
  morphism of the slice is that morphism itself.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Stack

section Pullback

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X Z Y₁ Y₂ : C}

/-- **Cutting a fibre product down along a morphism of the base is cartesian.** For `c : X ⟶ Z`,
`a : Y₁ ⟶ Y₂`, `b : Y₂ ⟶ Z` and `b' = a ≫ b`, the square whose bottom edge is `a`, whose
vertical edges are the second projections of `X ×_Z Y₁` and `X ×_Z Y₂`, and whose top edge is the
gap-filler out of `X ×_Z Y₁`, is cartesian. -/
theorem isPullback_liftPullbackSnd (c : X ⟶ Z) (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Z) (b' : Y₁ ⟶ Z)
    (hb : a ≫ b = b')
    (w : pullback.fst c b' ≫ c = (pullback.snd c b' ≫ a) ≫ b) :
    IsPullback ((IsPullback.of_hasPullback c b).lift (pullback.fst c b')
        (pullback.snd c b' ≫ a) w)
      (pullback.snd c b') (pullback.snd c b) a := by
  subst hb
  exact IsPullback.of_right' (IsPullback.of_hasPullback c (a ≫ b))
    (IsPullback.of_hasPullback c b)

end Pullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {W U : BigFppfOver B S hS} (c : W ⟶ U)
  (hc : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map c) d)

/-- The degree-`d` finite locally free cover of `T` obtained by base changing `c : W ⟶ U` along
an object `T ⟶ U` of the slice of the big fppf site of `S` at `U`. -/
noncomputable def finiteCoverPointObj (A : Over U) : FiniteCover B S hS d where
  U := A.left
  Z := pullback c A.hom
  q := pullback.snd c A.hom
  finiteLocallyFree :=
    letI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map c) d := hc
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      ((IsPullback.of_hasPullback c A.hom).map (BigFppfOver.toScheme B S hS))

/-- The morphism of degree-`d` covers obtained by base changing `c : W ⟶ U` along a morphism of
the slice of the big fppf site of `S` at `U`: its base component is the morphism itself and its
cover component is the gap-filler of the fibre-product square over the target. -/
noncomputable def finiteCoverPointMap {A₁ A₂ : Over U} (h : A₁ ⟶ A₂) :
    finiteCoverPointObj c hc A₁ ⟶ finiteCoverPointObj c hc A₂ where
  f := h.left
  g := (IsPullback.of_hasPullback c A₂.hom).lift (pullback.fst c A₁.hom)
    (pullback.snd c A₁.hom ≫ h.left)
    (((IsPullback.of_hasPullback c A₁.hom).w).trans
      (((Category.assoc (pullback.snd c A₁.hom) h.left A₂.hom).trans
        (congrArg (fun k => pullback.snd c A₁.hom ≫ k) (Over.w h))).symm))
  square := isPullback_liftPullbackSnd c h.left A₂.hom A₁.hom (Over.w h) _

/-- The base component of `finiteCoverPointMap c hc h` is `h.left`. -/
@[simp]
theorem finiteCoverPointMap_f {A₁ A₂ : Over U} (h : A₁ ⟶ A₂) :
    (finiteCoverPointMap c hc h).f = h.left :=
  rfl

/-- The cover component of `finiteCoverPointMap c hc h` commutes with the first projections. -/
@[simp]
theorem finiteCoverPointMap_g_comp_fst {A₁ A₂ : Over U} (h : A₁ ⟶ A₂) :
    (finiteCoverPointMap c hc h).g ≫ pullback.fst c A₂.hom = pullback.fst c A₁.hom :=
  (IsPullback.of_hasPullback c A₂.hom).lift_fst _ _ _

/-- The cover component of `finiteCoverPointMap c hc h` followed by the second projection is the
second projection followed by `h.left`. -/
@[simp]
theorem finiteCoverPointMap_g_comp_snd {A₁ A₂ : Over U} (h : A₁ ⟶ A₂) :
    (finiteCoverPointMap c hc h).g ≫ pullback.snd c A₂.hom =
      pullback.snd c A₁.hom ≫ h.left :=
  (IsPullback.of_hasPullback c A₂.hom).lift_snd _ _ _

/-- Base changing `c` along an identity of the slice is an identity of `ℋ_d`. -/
theorem finiteCoverPointMap_id (A : Over U) :
    finiteCoverPointMap c hc (𝟙 A) = 𝟙 (finiteCoverPointObj c hc A) := by
  refine FiniteCover.Hom.ext rfl ?_
  refine (IsPullback.of_hasPullback c A.hom).hom_ext ?_ ?_
  · exact (finiteCoverPointMap_g_comp_fst c hc (𝟙 A)).trans (Category.id_comp _).symm
  · exact (finiteCoverPointMap_g_comp_snd c hc (𝟙 A)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Base changing `c` along a composite of the slice is the composite of the base changes. -/
theorem finiteCoverPointMap_comp {A₁ A₂ A₃ : Over U} (h₁ : A₁ ⟶ A₂) (h₂ : A₂ ⟶ A₃) :
    finiteCoverPointMap c hc (h₁ ≫ h₂) =
      finiteCoverPointMap c hc h₁ ≫ finiteCoverPointMap c hc h₂ := by
  refine FiniteCover.Hom.ext rfl ?_
  refine (IsPullback.of_hasPullback c A₃.hom).hom_ext ?_ ?_
  · refine (finiteCoverPointMap_g_comp_fst c hc (h₁ ≫ h₂)).trans ?_
    refine ((Category.assoc _ _ _).trans ?_).symm
    refine (congrArg (fun k => (finiteCoverPointMap c hc h₁).g ≫ k)
      (finiteCoverPointMap_g_comp_fst c hc h₂)).trans ?_
    exact finiteCoverPointMap_g_comp_fst c hc h₁
  · refine (finiteCoverPointMap_g_comp_snd c hc (h₁ ≫ h₂)).trans ?_
    refine ((Category.assoc _ _ _).trans ?_).symm
    refine (congrArg (fun k => (finiteCoverPointMap c hc h₁).g ≫ k)
      (finiteCoverPointMap_g_comp_snd c hc h₂)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ h₂.left) (finiteCoverPointMap_g_comp_snd c hc h₁)).trans ?_
    exact Category.assoc _ _ _

/-- **The functor taking base changes of a fixed degree-`d` cover.** It sends an object `T ⟶ U`
of the slice of the big fppf site of `S` at `U` to the base change `W ×_U T ⟶ T` of `c`, and a
morphism of the slice to the morphism of covers whose base component is that morphism. -/
noncomputable def finiteCoverPointFunctor : Over U ⥤ FiniteCover B S hS d where
  obj A := finiteCoverPointObj c hc A
  map h := finiteCoverPointMap c hc h
  map_id A := finiteCoverPointMap_id c hc A
  map_comp h₁ h₂ := finiteCoverPointMap_comp c hc h₁ h₂

/-- The base of the cover attached to `T ⟶ U` is `T`. -/
@[simp]
theorem finiteCoverPointFunctor_obj_U (A : Over U) :
    ((finiteCoverPointFunctor c hc).obj A).U = A.left :=
  rfl

/-- The cover attached to `T ⟶ U` is the second projection of the fibre product of `c` with
`T ⟶ U`. -/
@[simp]
theorem finiteCoverPointFunctor_obj_q (A : Over U) :
    ((finiteCoverPointFunctor c hc).obj A).q = pullback.snd c A.hom :=
  rfl

/-- The base component of the image of a morphism `h` of the slice is `h.left`. -/
@[simp]
theorem finiteCoverPointFunctor_map_f {A₁ A₂ : Over U} (h : A₁ ⟶ A₂) :
    ((finiteCoverPointFunctor c hc).map h).f = h.left :=
  rfl

/-- **A degree-`d` cover of `U` gives a 1-morphism from the category represented by `U` to
`ℋ_d`**, over the big fppf site of `S`. -/
noncomputable def finiteCoverPoint :
    (schemeFibredCategory B S hS U).val ⥤ᵇ (finiteCoverFibered B S hS d).val where
  toFunctor := finiteCoverPointFunctor c hc
  w := rfl

/-- The underlying functor of `finiteCoverPoint c hc` is `finiteCoverPointFunctor c hc`. -/
@[simp]
theorem finiteCoverPoint_toFunctor :
    (finiteCoverPoint c hc).toFunctor = finiteCoverPointFunctor c hc :=
  rfl

/-- `AlgebraicGeometry.Stack.finiteCoverPoint` read as a 1-morphism of the 2-category of
categories fibred in groupoids over the big fppf site of `S`. -/
noncomputable def finiteCoverPointHom :
    schemeFibredCategory B S hS U ⟶ finiteCoverFibered B S hS d :=
  Bicategory.InducedBicategory.mkHom (finiteCoverPoint c hc)

/-- The underlying 1-morphism of `finiteCoverPointHom c hc` is `finiteCoverPoint c hc`. -/
@[simp]
theorem finiteCoverPointHom_hom :
    (finiteCoverPointHom c hc).hom = finiteCoverPoint c hc :=
  rfl

end AlgebraicGeometry.Stack

end
