module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianDatumSplitting
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianEndgame

/-!
# A descent datum split along two complementary invariant opens descends to a coproduct

Let `f : X ⟶ S` be a morphism of schemes and `(V, φ)` a descent datum relative to `X/S`. Suppose
`V = W ⊔ W'` for two complementary opens which are invariant under `φ`, so that the restrictions
`(W, φ|)` and `(W', φ|)` are descent data in their own right
(`AlgebraicGeometry.DescentDatum.restrictOpen`). If `U` descends `(W, φ|)` and `U'` descends
`(W', φ|)`, then the coproduct `U ⨿ U'` descends `(V, φ)`, with projection `V ⟶ U ⨿ U'` defined
piecewise on the two opens.

## Main definitions

* `AlgebraicGeometry.DescentDatum.descendedOfIsCompl`: **the scheme descending a datum split
  along two complementary invariant opens**, the coproduct of the schemes descending the two
  pieces.

## Main results

* `AlgebraicGeometry.DescentDatum.isPullback_projOfIsCompl`: the piecewise projection exhibits
  `V` as `(U ⨿ U') ×_S X`.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isCompl`: **a datum whose restrictions to
  two complementary invariant opens are étale effective is étale effective.**

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **A morphism out of a binary coproduct of schemes is étale when it is étale on each
summand.** -/
theorem etale_coprod_desc {X Y Z : Scheme.{u}} (a : X ⟶ Z) (b : Y ⟶ Z) [Etale a] [Etale b] :
    Etale (coprod.desc a b) := by
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (coprodOpenCover.{u, 0} X Y) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · change Etale (coprod.inl ≫ coprod.desc a b)
    rw [coprod.inl_desc]
    infer_instance
  · change Etale (coprod.inr ≫ coprod.desc a b)
    rw [coprod.inr_desc]
    infer_instance

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

attribute [instance] etale_restrictOpen_over_hom

section Split

variable (W W' : D.over.left.Opens) (hWW' : IsCompl W W') {hW : D.IsTransitionInvariant W}
  {hW' : D.IsTransitionInvariant W'} (Q : (D.restrictOpen W hW).Descended)
  (Q' : (D.restrictOpen W' hW').Descended)

/-- The coproduct of the two descended schemes, as a scheme over `S`. -/
abbrev baseOfIsCompl : Over S := Over.mk (coprod.desc Q.base.hom Q'.base.hom)

/-- **The projection of `V` onto the coproduct of the descended schemes**, the projection of
`W` followed by the first summand on `W` and the projection of `W'` followed by the second
summand on `W'`. -/
def projOfIsCompl : D.over.left ⟶ Q.base.left ⨿ Q'.base.left :=
  (D.isColimitBinaryCofanOpens W W' hWW').desc
    (BinaryCofan.mk (P := Q.base.left ⨿ Q'.base.left) (X := W.toScheme) (Y := W'.toScheme)
      (Q.proj ≫ coprod.inl) (Q'.proj ≫ coprod.inr))

/-- On `W`, the projection `AlgebraicGeometry.DescentDatum.projOfIsCompl` is the projection of
`U` followed by the first summand inclusion. -/
@[reassoc]
lemma ι_comp_projOfIsCompl_left :
    W.ι ≫ D.projOfIsCompl W W' hWW' Q Q' = Q.proj ≫ coprod.inl :=
  (D.isColimitBinaryCofanOpens W W' hWW').fac _ ⟨WalkingPair.left⟩

/-- On `W'`, the projection `AlgebraicGeometry.DescentDatum.projOfIsCompl` is the projection of
`U'` followed by the second summand inclusion. -/
@[reassoc]
lemma ι_comp_projOfIsCompl_right :
    W'.ι ≫ D.projOfIsCompl W W' hWW' Q Q' = Q'.proj ≫ coprod.inr :=
  (D.isColimitBinaryCofanOpens W W' hWW').fac _ ⟨WalkingPair.right⟩

/-- **The piecewise projection exhibits `V` as the fibre product of the coproduct of the
descended schemes with `X` over `S`.** -/
theorem isPullback_projOfIsCompl :
    IsPullback D.over.hom (D.projOfIsCompl W W' hWW' Q Q') f
      (coprod.desc Q.base.hom Q'.base.hom) := by
  let Ub : WalkingPair → Scheme.{u} := fun j ↦ WalkingPair.casesOn j Q.base.left Q'.base.left
  let a : Cofan Ub := BinaryCofan.mk coprod.inl coprod.inr
  have hau : IsUniversalColimit a :=
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod Q.base.left Q'.base.left)).isUniversal
  let P : WalkingPair → Scheme.{u} := fun j ↦ WalkingPair.casesOn j W.toScheme W'.toScheme
  let d : Cofan P := BinaryCofan.mk W.ι W'.ι
  let hd : IsColimit d := D.isColimitBinaryCofanOpens W W' hWW'
  let fb : ∀ j, Ub j ⟶ S := fun j ↦ match j with
    | .left => Q.base.hom
    | .right => Q'.base.hom
  let q₁ : ∀ j, P j ⟶ Ub j := fun j ↦ match j with
    | .left => Q.proj
    | .right => Q'.proj
  let q₂ : ∀ j, P j ⟶ X := fun j ↦ match j with
    | .left => W.ι ≫ D.over.hom
    | .right => W'.ι ≫ D.over.hom
  have hP : ∀ j, IsPullback (q₁ j) (q₂ j) (fb j) f := fun j ↦ match j with
    | .left => Q.isPullback.flip
    | .right => Q'.isPullback.flip
  have key := hau.isPullback_of_isColimit_right fb (coprod.desc Q.base.hom Q'.base.hom) f q₁ q₂
    hP hd (fun j ↦ match j with
      | .left => coprod.inl_desc _ _
      | .right => coprod.inr_desc _ _)
  have h₂ : Cofan.IsColimit.desc hd q₂ = D.over.hom :=
    Cofan.IsColimit.hom_ext hd _ _ fun j ↦ match j with
      | .left => Cofan.IsColimit.fac hd q₂ .left
      | .right => Cofan.IsColimit.fac hd q₂ .right
  have h₁ : Cofan.IsColimit.desc hd (fun j ↦ q₁ j ≫ a.inj j) = D.projOfIsCompl W W' hWW' Q Q' :=
    Cofan.IsColimit.hom_ext hd _ _ fun j ↦ match j with
      | .left => (Cofan.IsColimit.fac hd _ .left).trans
          (D.ι_comp_projOfIsCompl_left W W' hWW' Q Q').symm
      | .right => (Cofan.IsColimit.fac hd _ .right).trans
          (D.ι_comp_projOfIsCompl_right W W' hWW' Q Q').symm
  rw [h₁, h₂] at key
  exact key.flip

/-- **The scheme descending a descent datum split along two complementary invariant opens**: the
coproduct `U ⨿ U'` of a scheme `U` descending the restriction to `W` and a scheme `U'`
descending the restriction to `W'`. -/
def descendedOfIsCompl : D.Descended :=
  descendedOfIsOpenCover (U := D.baseOfIsCompl W W' Q Q') (ι := ULift.{u} Bool)
    (W := fun b ↦ cond b.down W W')
    (TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ by
      rcases (union_coe_eq_univ_of_isCompl hWW').symm.subset (Set.mem_univ x) with h | h
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨true⟩, h⟩
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨false⟩, h⟩))
    (fun b ↦ match b with
      | ⟨true⟩ => hW
      | ⟨false⟩ => hW')
    (fun b ↦ match b with
      | ⟨true⟩ => Q
      | ⟨false⟩ => Q')
    (fun b ↦ match b with
      | ⟨true⟩ => coprod.inl
      | ⟨false⟩ => coprod.inr)
    (D.projOfIsCompl W W' hWW' Q Q') (D.isPullback_projOfIsCompl W W' hWW' Q Q')
    (fun b ↦ match b with
      | ⟨true⟩ => D.ι_comp_projOfIsCompl_left W W' hWW' Q Q'
      | ⟨false⟩ => D.ι_comp_projOfIsCompl_right W W' hWW' Q Q')

/-- The base of `AlgebraicGeometry.DescentDatum.descendedOfIsCompl` is the coproduct
`AlgebraicGeometry.DescentDatum.baseOfIsCompl`. -/
@[simp]
lemma descendedOfIsCompl_base :
    (D.descendedOfIsCompl W W' hWW' Q Q').base = D.baseOfIsCompl W W' Q Q' := rfl

/-- The projection of `AlgebraicGeometry.DescentDatum.descendedOfIsCompl` is
`AlgebraicGeometry.DescentDatum.projOfIsCompl`. -/
@[simp]
lemma descendedOfIsCompl_proj :
    (D.descendedOfIsCompl W W' hWW' Q Q').proj = D.projOfIsCompl W W' hWW' Q Q' := rfl

end Split

/-- **A descent datum whose restrictions to two complementary invariant opens are étale effective
is étale effective.** -/
theorem isEtaleEffective_of_isCompl [Etale D.over.hom] (W W' : D.over.left.Opens)
    (hWW' : IsCompl W W') (hW : D.IsTransitionInvariant W) (hW' : D.IsTransitionInvariant W')
    (h : IsEtaleEffective (D.restrictOpen W hW)) (h' : IsEtaleEffective (D.restrictOpen W' hW')) :
    IsEtaleEffective D := by
  let Q : (D.restrictOpen W hW).Descended :=
    Descended.ofIso ((IsEtaleDescentData f).ι.mapIso h.getIso)
  let Q' : (D.restrictOpen W' hW').Descended :=
    Descended.ofIso ((IsEtaleDescentData f).ι.mapIso h'.getIso)
  have _ : Etale Q.base.hom := h.witness.prop
  have _ : Etale Q'.base.hom := h'.witness.prop
  have _ : Etale (D.descendedOfIsCompl W W' hWW' Q Q').base.hom :=
    etale_coprod_desc Q.base.hom Q'.base.hom
  exact (D.descendedOfIsCompl W W' hWW' Q Q').isEtaleEffective

end DescentDatum

end AlgebraicGeometry

end
