module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Effective

/-!
# Descent data from transition maps

Let `{fᵢ : Uᵢ ⟶ T}` be a family of morphisms of algebraic spaces and `gᵢ : Yᵢ ⟶ Uᵢ` algebraic
spaces over its members. A descent datum on the `Yᵢ` (Stacks 0ADI) is the same as a family of
*transition maps* `Ψᵢⱼ : Yᵢ ×_T Uⱼ ⟶ Yⱼ` over `Uⱼ`, which move a point of `Yᵢ` to `Yⱼ` along a
point of `Uⱼ` with the same image in `T`, such that moving a point of `Yᵢ` to its own image in `Uᵢ`
does nothing and moving twice is moving once. This file builds the move operation
(`CategoryTheory.FamilyTransport`) and the descent datum from such maps.

This is the form in which the local stabilizations of a prestable family (Stacks 0E8A) are glued:
the transition maps are the isomorphisms between two stabilizations over the overlaps, and the
two laws follow from the uniqueness of morphisms out of the target of a contraction.

## Main definitions

* `AlgebraicGeometry.Space.Descent.transitionMove`: the point of `Yⱼ` obtained by moving.
* `AlgebraicGeometry.Space.Descent.transitionTransport`: the move operation.
* `AlgebraicGeometry.Space.Descent.transitionDescentData`: the descent datum.

## References

* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type v} {U : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (f : ∀ i, U i ⟶ T) {Y : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : ∀ i, Y i ⟶ U i)
  (Ψ : ∀ i j, pullback (g i ≫ f i) (f j) ⟶ Y j)

/-- **Moving a point along the transition maps.** A point `a` of `Yᵢ` and a point `b` of `Uⱼ`
with the same image in `T` give the point `Ψᵢⱼ (a, b)` of `Yⱼ`. -/
def transitionMove {i j : ι} {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U j)
    (hab : a ≫ g i ≫ f i = b ≫ f j) : W ⟶ Y j :=
  pullback.lift a b hab ≫ Ψ i j

variable {f g Ψ}

/-- Precomposing a map into a pullback with `k` precomposes both of its components. -/
private theorem comp_pullback_lift {C : Type*} [Category C] {X Y Z W W' : C} {f : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] (k : W' ⟶ W) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    k ≫ pullback.lift a b h =
      pullback.lift (k ≫ a) (k ≫ b) (by rw [Category.assoc, h, Category.assoc]) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- Moving is compatible with precomposition: precomposing the moved point `Ψᵢⱼ (a, b)` with
`k : W' ⟶ W` gives the point obtained by moving `k ≫ a` along `k ≫ b`. -/
theorem comp_transitionMove {i j : ι} {W W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : W' ⟶ W)
    (a : W ⟶ Y i) (b : W ⟶ U j) (hab : a ≫ g i ≫ f i = b ≫ f j) :
    k ≫ transitionMove f g Ψ a b hab =
      transitionMove f g Ψ (k ≫ a) (k ≫ b) (by rw [Category.assoc, hab, Category.assoc]) := by
  simp only [transitionMove, ← Category.assoc, comp_pullback_lift]

variable (hΨ : ∀ i j, Ψ i j ≫ g j = pullback.snd _ _)

include hΨ in
/-- If `Ψᵢⱼ ≫ gⱼ` is the second projection `Yᵢ ×_T Uⱼ ⟶ Uⱼ`, then the moved point `Ψᵢⱼ (a, b)`
of `Yⱼ` maps to `b` in `Uⱼ`. -/
@[reassoc]
theorem transitionMove_comp {i j : ι} {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i)
    (b : W ⟶ U j) (hab : a ≫ g i ≫ f i = b ≫ f j) :
    transitionMove f g Ψ a b hab ≫ g j = b := by
  rw [transitionMove, Category.assoc, hΨ, pullback.lift_snd]

/-- If `Ψᵢᵢ` restricts to the identity on the diagonal `(1, gᵢ) : Yᵢ ⟶ Yᵢ ×_T Uᵢ`, then moving
a point `a` of `Yᵢ` along its own image `a ≫ gᵢ` gives back `a`. -/
theorem transitionMove_self
    (hself : ∀ i, pullback.lift (𝟙 (Y i)) (g i) (by simp) ≫ Ψ i i = 𝟙 (Y i)) {i : ι}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U i) (hb : b = a ≫ g i)
    (hab : a ≫ g i ≫ f i = b ≫ f i) : transitionMove f g Ψ a b hab = a := by
  subst hb
  have h := congrArg (fun m => a ≫ m) (hself i)
  simp only [Category.comp_id] at h
  refine Eq.trans ?_ h
  simp only [transitionMove, ← Category.assoc, comp_pullback_lift, Category.comp_id]

/-- **The move operation of a family of transition maps.** In the category of presheaves over
`T`, a point of `Yᵢ` is moved to `Yⱼ` along a point of `Uⱼ`, provided moving a point to its own
image does nothing (`hself`) and moving twice is moving once (`hcomp`). -/
def transitionTransport
    (hself : ∀ i, pullback.lift (𝟙 (Y i)) (g i) (by simp) ≫ Ψ i i = 𝟙 (Y i))
    (hcomp : ∀ (i j k : ι) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U j)
      (c : W ⟶ U k) (hab : a ≫ g i ≫ f i = b ≫ f j) (hac : a ≫ g i ≫ f i = c ≫ f k),
      transitionMove f g Ψ (transitionMove f g Ψ a b hab) c
          (by rw [transitionMove_comp_assoc hΨ, ← hab, hac]) =
        transitionMove f g Ψ a c hac) :
    FamilyTransport (fun i => (Over.map (f i)).obj (Over.mk (g i))) (fun i => Over.mk (f i))
      (fun i => structureMap (f i) (Over.mk (g i))) where
  move {i j Z} v y := Over.homMk (transitionMove f g Ψ v.left y.left (by
      have hv := Over.w v
      have hy := Over.w y
      simp only [Over.map_obj_hom, Over.mk_hom] at hv hy
      rw [hv, hy])) (by
      have hy := Over.w y
      simp only [Over.map_obj_hom, Over.mk_hom] at hy ⊢
      rw [← Category.assoc, transitionMove_comp hΨ, hy])
  comp_move {i j Z W} k v y := by
    apply Over.OverMorphism.ext
    change k.left ≫ transitionMove f g Ψ v.left y.left _ =
      transitionMove f g Ψ (k ≫ v).left (k ≫ y).left _
    rw [comp_transitionMove]
    congr 1
  move_base {i j Z} v y := Over.OverMorphism.ext (transitionMove_comp hΨ _ _ _)
  move_self {i Z} v :=
    Over.OverMorphism.ext (transitionMove_self hself v.left _ (by simp [structureMap]) _)
  move_comp {i j k Z} v y z := Over.OverMorphism.ext (hcomp i j k v.left y.left z.left _ _)

/-- **The descent datum of a family of transition maps.** -/
def transitionDescentData (hT : IsAlgebraicSpace B S hS T) (hU : ∀ i, IsAlgebraicSpace B S hS (U i))
    (hY : ∀ i, IsAlgebraicSpace B S hS (Y i))
    (hself : ∀ i, pullback.lift (𝟙 (Y i)) (g i) (by simp) ≫ Ψ i i = 𝟙 (Y i))
    (hcomp : ∀ (i j k : ι) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U j)
      (c : W ⟶ U k) (hab : a ≫ g i ≫ f i = b ≫ f j) (hac : a ≫ g i ≫ f i = c ≫ f k),
      transitionMove f g Ψ (transitionMove f g Ψ a b hab) c
          (by rw [transitionMove_comp_assoc hΨ, ← hab, hac]) =
        transitionMove f g Ψ a c hac) :
    DescentData f hT hU where
  obj i := Over.mk (g i)
  obj_isAlgebraicSpace i := hY i
  gluing i j := (transitionTransport hΨ hself hcomp).gluing i j
  cocycle i j k := (transitionTransport hΨ hself hcomp).gluing_cocycle i j k

end AlgebraicGeometry.Space.Descent

end
