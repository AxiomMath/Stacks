module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.TransitionMapDescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveFiniteTypeCovering

/-!
# Gluing algebraic spaces along transition maps

Let `{fᵢ : Uᵢ ⟶ T}` be an fppf covering of algebraic spaces and `gᵢ : Yᵢ ⟶ Uᵢ` algebraic spaces of
finite type over its members, with transition maps `Ψᵢⱼ : Yᵢ ×_T Uⱼ ⟶ Yⱼ` satisfying the unit
and cocycle laws. Then the `Yᵢ` glue: there are an algebraic space `Q ⟶ T` and morphisms
`rᵢ : Yᵢ ⟶ Q` exhibiting each `Yᵢ` as `Q ×_T Uᵢ`, and the transition maps become the identity of
`Q`: moving a point of `Yᵢ` to `Yⱼ` does not change its image in `Q`. This is Stacks 0ADV, part
(2), applied to the descent datum of the transition maps
(`AlgebraicGeometry.Space.Descent.transitionDescentData`), read through the equivalence of
Stacks 0ADT between descent data and sheaves over `T`.

## Main results

* `AlgebraicGeometry.Space.Descent.exists_glued_of_transitions`

## References

* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type v} {U : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {f : ∀ i, U i ⟶ T} {Y : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : ∀ i, Y i ⟶ U i}
  {Ψ : ∀ i j, pullback (g i ≫ f i) (f j) ⟶ Y j}

/-- **Gluing along transition maps.** For an fppf covering `{fᵢ : Uᵢ ⟶ T}`, algebraic spaces
`gᵢ : Yᵢ ⟶ Uᵢ` of finite type and transition maps `Ψᵢⱼ : Yᵢ ×_T Uⱼ ⟶ Yⱼ` over `Uⱼ` satisfying the
unit and cocycle laws, there are an algebraic space `Q` over `T` and morphisms `rᵢ : Yᵢ ⟶ Q`
making every square `Yᵢ ⟶ Q, Yᵢ ⟶ Uᵢ` cartesian over `T`, such that moving a point of `Yᵢ` along
the transition maps does not change its image in `Q`. -/
theorem exists_glued_of_transitions (hcov : IsFppfCovering B S hS U f)
    (hΨ : ∀ i j, Ψ i j ≫ g j = pullback.snd _ _)
    (hY : ∀ i, IsAlgebraicSpace B S hS (Y i)) (hft : ∀ i, IsFiniteType B S hS (g i))
    (hself : ∀ i, pullback.lift (𝟙 (Y i)) (g i) (by simp) ≫ Ψ i i = 𝟙 (Y i))
    (hcomp : ∀ (i j k : ι) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U j)
      (c : W ⟶ U k) (hab : a ≫ g i ≫ f i = b ≫ f j) (hac : a ≫ g i ≫ f i = c ≫ f k),
      transitionMove f g Ψ (transitionMove f g Ψ a b hab) c
          (by rw [transitionMove_comp_assoc hΨ, ← hab, hac]) =
        transitionMove f g Ψ a c hac) :
    ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : Q ⟶ T) (r : ∀ i, Y i ⟶ Q),
      IsAlgebraicSpace B S hS Q ∧ (∀ i, IsPullback (r i) (g i) q (f i)) ∧
      ∀ (i j : ι) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ Y i) (b : W ⟶ U j)
        (hab : a ≫ g i ≫ f i = b ≫ f j), transitionMove f g Ψ a b hab ≫ r j = a ≫ r i := by
  let D := transitionDescentData hΨ hcov.target_isAlgebraicSpace hcov.source_isAlgebraicSpace hY
    hself hcomp
  have heff : D.IsEffective := DescentData.isEffective_of_isFiniteType D hcov hft
  let E := fppfDescentDataSheafEquivalence f hcov
  refine ⟨(E.inverse.obj D).obj.left, (E.inverse.obj D).obj.hom,
    fun i => descentInclusion f hcov D i,
    (isAlgebraicSpace_inverse_iff_isEffective f hcov D).2 heff,
    fun i => isPullback_descentInclusion f hcov D i, ?_⟩
  intro i j W a b hab
  -- the move operations, read through the counit of the equivalence
  let κ : D ⟶ (fibreDescentFunctor f hcov.target_isAlgebraicSpace
      hcov.source_isAlgebraicSpace).obj (E.inverse.obj D) := (E.counitIso.app D).inv
  let Z : Over T := Over.mk (a ≫ g i ≫ f i)
  let v : Z ⟶ (Over.map (f i)).obj (D.obj i) := Over.homMk a rfl
  let y : Z ⟶ Over.mk (f j) := Over.homMk b hab.symm
  have hlift : ∀ {A Bb : ι → Over T} {p : ∀ i, A i ⟶ Bb i} (t : FamilyTransport A Bb p) {i j : ι}
      {Z : Over T} (v : Z ⟶ A i) (y : Z ⟶ Bb j),
      prod.lift v y ≫ (t.gluing i j).hom.left ≫ prod.snd = t.move v y := by
    intro A Bb p t i j Z v y
    rw [FamilyTransport.gluing_hom, prod.lift_snd, t.comp_move, prod.lift_fst, prod.lift_snd]
  let F := (E.inverse.obj D).obj
  let w := v ≫ (Over.map (f i)).map (κ.hom i)
  have h1 : D.transport.move v y = (transitionTransport hΨ hself hcomp).move v y :=
    (DescentData.transport_move D v y).trans (hlift (transitionTransport hΨ hself hcomp) v y)
  have h2 : ((fibreDescentFunctor f hcov.target_isAlgebraicSpace
      hcov.source_isAlgebraicSpace).obj (E.inverse.obj D)).transport.move w y =
        fibreMove f F w y :=
    (DescentData.transport_move _ w y).trans (hlift (fibreTransport f F) w y)
  have H := DescentData.move_naturality κ v y
  rw [h1, h2] at H
  have H' : ((transitionTransport hΨ hself hcomp).move v y ≫
      (Over.map (f j)).map (κ.hom j)).left ≫ pullback.fst F.hom (f j) =
        (fibreMove f F w y).left ≫ pullback.fst F.hom (f j) :=
    congrArg (fun m => m.left ≫ pullback.fst F.hom (f j)) H
  exact (Category.assoc _ _ _).symm.trans
    ((H'.trans (fibreMove_left_fst f F w y)).trans (Category.assoc _ _ _))

end AlgebraicGeometry.Space.Descent

end
