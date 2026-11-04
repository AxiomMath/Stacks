module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# The reduction of a formal algebraic space, and surjectivity

Let `S` be a scheme contained in a big fppf site `B`. A *reduction* of a formal algebraic space
`X` over `S` is a reduced algebraic space `X_red` together with a representable morphism
`i : X_red ⟶ X` which is a thickening and through which every morphism from a reduced algebraic
space factors uniquely. This is the datum that Stacks 0AIN asserts to exist for every formal
algebraic space.

For a morphism `f : X ⟶ Y` of formal algebraic spaces over `S` which is representable by
algebraic spaces, `f` is surjective in the sense of Stacks 03XZ exactly when the induced
morphism `X_red ⟶ Y_red` is a surjective morphism of algebraic spaces. The reason is that the
inclusion of a reduction is bijective on points: a field-valued point of `X` is a section over
the spectrum of a field, which is reduced, so the thickening base-changed to it is an
isomorphism and the point lifts uniquely to the reduction.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsReduction` is the predicate that a morphism of fppf sheaves
  exhibits its source as a reduction of its target.

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.bijective_pointsMapULift`: the inclusion of a
  reduction is bijective on points.
* `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSurjectiveULift_iff`: a morphism of fppf
  sheaves representable by algebraic spaces is surjective in the sense of Stacks 03XZ exactly
  when it is surjective on points.
* `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSurjectiveULift_iff_isSurjectiveULift_red`:
  **Stacks 0GB8**.

## Implementation notes

`AlgebraicGeometry.FormalSpace.IsReduction` is only the predicate naming the defining
properties of a reduction, and carries no Stacks tag: the tag 0AIN is the existence statement,
which is `AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence`. Accordingly Stacks 0GB8 is stated
with the two reductions, their inclusions and the morphism between them supplied as hypotheses.
That is more general than the statement about a chosen reduction, which it implies, and it needs
no choice.

Surjectivity of a morphism of algebraic spaces is, by Stacks 03ME, surjectivity of the induced
map on points, so the right-hand side of Stacks 0GB8 is
`AlgebraicGeometry.Space.IsSurjectiveULift`, and the left-hand side is the condition of
Stacks 03XZ at that property, which is `AlgebraicGeometry.Space.HasPropertyULift`. Both are the
notions of `StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective` and
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued` for a value universe independent of the
universe of the schemes, since a formal algebraic space is a sheaf of `Type (u + 1)`.

The representability clause and the base-change clause of the thickening condition are separate
fields, as they are two separate assertions of the source; together they are
`AlgebraicGeometry.Space.IsRepresentableThickeningULift`, which is
`AlgebraicGeometry.FormalSpace.IsReduction.isRepresentableThickening`.

Once the two reductions are given, the hypothesis that the source and target of the morphism be
formal algebraic spaces is not needed: everything the argument uses about them is already
contained in the reduction data. The hypotheses are nevertheless part of the statement, as they
are part of the source statement, and are marked as unused.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `i : Xred ⟶ X` of fppf sheaves on the big fppf site of `S` *exhibits `Xred` as a
reduction of `X`* when `Xred` is a reduced algebraic space, `i` is representable and a
thickening, and every morphism to `X` from a reduced algebraic space factors uniquely
through `i`. These are the defining properties of the reduction of a formal algebraic space. -/
structure IsReduction (X Xred : FppfSheaf B S hS) (i : Xred ⟶ X) : Prop where
  /-- The source is an algebraic space. -/
  algebraic : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Xred.obj
  /-- The source is reduced, in the étale-local sense of Stacks 03E6. -/
  reduced : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS Xred.obj
    (fun T : Scheme.{u} ↦ IsReduced T)
  /-- The morphism is representable, relative to the universe-lifted Yoneda embedding. -/
  representable :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).relativelyRepresentable i.hom
  /-- The morphism of schemes underlying every represented base change is a thickening. -/
  thickening : ∀ ⦃a b : BigFppfOver B S hS⦄ (g : (uliftYoneda.{u + 1}).obj a ⟶ X.obj)
    (fst : (uliftYoneda.{u + 1}).obj b ⟶ Xred.obj) (snd : b ⟶ a),
    IsPullback fst ((uliftYoneda.{u + 1}).map snd) i.hom g →
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map snd)
  /-- Every morphism to `X` from a reduced algebraic space factors uniquely through `i`. -/
  universal : ∀ U : FppfSheaf B S hS, Space.IsAlgebraicSpaceULift.{u + 1} B S hS U.obj →
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS U.obj (fun T : Scheme.{u} ↦ IsReduced T) →
    ∀ f : U ⟶ X, ∃! g : U ⟶ Xred, g ≫ i = f

namespace IsReduction

variable {B S hS}
variable {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}

/-- The inclusion of a reduction is a representable thickening. -/
theorem isRepresentableThickening (h : IsReduction B S hS X Xred i) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom :=
  ⟨h.representable, h.thickening⟩

/-- A section of `X` over an object of the site with reduced underlying scheme lifts uniquely
along the inclusion of a reduction: the base change of the thickening to that object is a
surjective closed immersion into a reduced scheme, hence an isomorphism. -/
theorem existsUnique_comp_eq (h : IsReduction B S hS X Xred i) (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (v : X.obj.obj (Opposite.op T)) :
    ∃! l : (uliftYoneda.{u + 1}).obj T ⟶ Xred.obj,
      l ≫ i.hom = uliftYonedaEquiv.{u + 1}.symm v := by
  obtain ⟨b, snd, fst, sq⟩ := h.representable (uliftYonedaEquiv.{u + 1}.symm v)
  obtain ⟨hclosed, hsurj⟩ := h.thickening _ fst snd sq
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) := hclosed
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map snd) := ⟨hsurj⟩
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
    isIso_of_isClosedImmersion_of_surjective _
  have _ : IsIso snd := isIso_of_reflects_iso snd (BigFppfOver.toScheme B S hS)
  have _ : IsIso ((uliftYoneda.{u + 1}).map snd) := inferInstance
  refine ⟨inv ((uliftYoneda.{u + 1}).map snd) ≫ fst, ?_, ?_⟩
  · show (inv ((uliftYoneda.{u + 1}).map snd) ≫ fst) ≫ i.hom
        = uliftYonedaEquiv.{u + 1}.symm v
    rw [Category.assoc, sq.w, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · intro l hl
    have hw : l ≫ i.hom = 𝟙 _ ≫ uliftYonedaEquiv.{u + 1}.symm v := by
      rwa [Category.id_comp]
    have hm : sq.lift l (𝟙 _) hw = inv ((uliftYoneda.{u + 1}).map snd) :=
      (cancel_mono ((uliftYoneda.{u + 1}).map snd)).mp
        (by rw [sq.lift_snd, IsIso.inv_hom_id])
    rw [← sq.lift_fst l (𝟙 _) hw, hm]

/-- The inclusion of a reduction is bijective on the sections over an object of the site whose
underlying scheme is reduced. -/
theorem bijective_app (h : IsReduction B S hS X Xred i) (T : BigFppfOver B S hS)
    (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T)) :
    Function.Bijective (i.hom.app (Opposite.op T)) := by
  constructor
  · intro a₁ a₂ he
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    obtain ⟨l, hl, hu⟩ := h.existsUnique_comp_eq T hT (i.hom.app (Opposite.op T) a₁)
    have e₂ : uliftYonedaEquiv.{u + 1}.symm a₂ ≫ i.hom
        = uliftYonedaEquiv.{u + 1}.symm (i.hom.app (Opposite.op T) a₁) := by
      rw [uliftYonedaEquiv_symm_comp, he]
    rw [hu _ (uliftYonedaEquiv_symm_comp a₁ i.hom), hu _ e₂]
  · intro v
    obtain ⟨l, hl, -⟩ := h.existsUnique_comp_eq T hT v
    refine ⟨uliftYonedaEquiv.{u + 1} l, ?_⟩
    have := congrArg uliftYonedaEquiv.{u + 1} hl
    rwa [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] at this

/-- The underlying scheme of the object of the site carrying a field-valued point is the
spectrum of a field, hence reduced. -/
private theorem isReduced_toScheme_obj_siteObject
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))
    (p : Space.FieldValuedPointULift.{u + 1} B S hS F) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS F)) :=
  inferInstanceAs (IsReduced (Spec (.of p.carrier)))

/-- A field-valued point of `G` over a section `v` of `F` that `φ` sends to its value is the image
under `φ` of the point of `F` with value `v`. -/
private theorem pointsMapULift_mk_eq_mk
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G)
    (point : Space.FieldValuedPointULift.{u + 1} B S hS G)
    (v : F.obj (Opposite.op (point.siteObject B S hS G)))
    (hv : φ.app (Opposite.op (point.siteObject B S hS G)) v = point.value) :
    Space.pointsMapULift.{u + 1} B S hS F φ
      (Quot.mk _ ⟨point.carrier, point.contained, point.toBase, v⟩) = Quot.mk _ point := by
  refine Quot.sound ⟨point, ⟨𝟙 _, ?_⟩, ⟨𝟙 _, by simp⟩⟩
  change G.map (𝟙 (point.siteObject B S hS G)).op (φ.app _ v) = point.value
  simpa using hv

/-- The inclusion of a reduction is bijective on points: every field-valued point of `X` is a
section over the spectrum of a field, which is reduced, so it lifts uniquely to the
reduction. -/
theorem bijective_pointsMapULift (h : IsReduction B S hS X Xred i) :
    Function.Bijective (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom) := by
  constructor
  · intro first second equality
    induction first using Quot.ind with | _ first =>
    induction second using Quot.ind with | _ second =>
    obtain ⟨common, ⟨toFirst, hfirst⟩, ⟨toSecond, hsecond⟩⟩ :=
      (Space.FieldValuedPointULift.class_eq_class_iff B S hS X.obj _ _).mp equality
    have hred := isReduced_toScheme_obj_siteObject X.obj common
    obtain ⟨value, hvalue⟩ := (h.bijective_app _ hred).2 common.value
    refine Quot.sound ⟨⟨common.carrier, common.contained, common.toBase, value⟩,
      ⟨toFirst, ?_⟩, ⟨toSecond, ?_⟩⟩ <;>
    · apply (h.bijective_app _ hred).1
      rw [NatTrans.naturality_apply, hvalue]
      assumption
  · intro point
    induction point using Quot.ind with | _ point =>
    have hred := isReduced_toScheme_obj_siteObject X.obj point
    obtain ⟨value, hvalue⟩ := (h.bijective_app _ hred).2 point.value
    exact ⟨_, pointsMapULift_mk_eq_mk i.hom point value hvalue⟩

end IsReduction

variable {B S hS}

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by algebraic
spaces is surjective in the sense of Stacks 03XZ exactly when it is surjective on points. -/
theorem hasPropertyULift_isSurjectiveULift_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f) :
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsSurjectiveULift.{u + 1} B S hS g.hom) f hf ↔
      Space.IsSurjectiveULift.{u + 1} B S hS f := by
  constructor
  · intro hsurj point
    induction point using Quot.ind with | _ point =>
    let T := point.siteObject B S hS G
    let ξ : (uliftYoneda.{u + 1}).obj T ⟶ G := uliftYonedaEquiv.{u + 1}.symm point.value
    let q : Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj T) :=
      ⟨point.carrier, point.contained, point.toBase, ULift.up (𝟙 T)⟩
    obtain ⟨lifted, hlifted⟩ := hsurj T ξ (Quot.mk _ q)
    refine ⟨Space.pointsMapULift B S hS _ (pullback.snd ξ f) lifted, ?_⟩
    have hξ : Space.pointsMapULift B S hS ((uliftYoneda.{u + 1}).obj T) ξ (Quot.mk _ q)
        = Quot.mk _ point := by
      exact IsReduction.pointsMapULift_mk_eq_mk ξ point (ULift.up (𝟙 T)) (by simp [ξ, T])
    calc Space.pointsMapULift B S hS F f
          (Space.pointsMapULift B S hS _ (pullback.snd ξ f) lifted)
        = Space.pointsMapULift B S hS _ (pullback.snd ξ f ≫ f) lifted := by
          rw [Space.pointsMapULift_comp]
          rfl
      _ = Space.pointsMapULift B S hS _ (pullback.fst ξ f ≫ ξ) lifted := by
          rw [pullback.condition]
      _ = Space.pointsMapULift B S hS ((uliftYoneda.{u + 1}).obj T) ξ
            (Space.pointsMapULift B S hS _ (pullback.fst ξ f) lifted) := by
          rw [Space.pointsMapULift_comp]
          rfl
      _ = Quot.mk _ point := by
          have hlifted' : Space.pointsMapULift.{u + 1} B S hS (pullback ξ f)
              (pullback.fst ξ f) lifted = Quot.mk _ q := hlifted
          rwa [hlifted']
  · intro hsurj U ξ point
    obtain ⟨pre, hpre⟩ := hsurj (Space.pointsMapULift B S hS _ ξ point)
    obtain ⟨v, hv, -⟩ := Space.exists_point_of_isPullbackULift B S hS
      (IsPullback.of_hasPullback ξ f) point pre hpre.symm
    exact ⟨v, hv⟩

/-- **Stacks 0GB8.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which is
representable by algebraic spaces, let `iX : Xred ⟶ X` and `iY : Yred ⟶ Y` be reductions and let
`fred : Xred ⟶ Yred` be compatible with `f`. Then `f` is surjective in the sense of Stacks 03XZ
if and only if `fred` is a surjective morphism of algebraic spaces. -/
@[stacks 0GB8]
theorem hasPropertyULift_isSurjectiveULift_iff_isSurjectiveULift_red
    {X Y : FppfSheaf B S hS}
    (_hX : IsFormalAlgebraicSpace B S hS X) (_hY : IsFormalAlgebraicSpace B S hS Y)
    {Xred Yred : FppfSheaf B S hS} {iX : Xred ⟶ X} {iY : Yred ⟶ Y}
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    {fred : Xred ⟶ Yred} (hfred : fred ≫ iY = iX ≫ f) :
    Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsSurjectiveULift.{u + 1} B S hS g.hom) f.hom hf ↔
      Space.IsSurjectiveULift.{u + 1} B S hS fred.hom := by
  rw [hasPropertyULift_isSurjectiveULift_iff f.hom hf]
  have hYbij := hiY.bijective_pointsMapULift
  have hhom : fred.hom ≫ iY.hom = iX.hom ≫ f.hom := congrArg (·.hom) hfred
  have hcomm : ∀ pt, Space.pointsMapULift.{u + 1} B S hS Yred.obj iY.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred.obj fred.hom pt)
      = Space.pointsMapULift.{u + 1} B S hS X.obj f.hom
        (Space.pointsMapULift.{u + 1} B S hS Xred.obj iX.hom pt) := by
    intro pt
    have h₁ : Space.pointsMapULift.{u + 1} B S hS Xred.obj (fred.hom ≫ iY.hom) pt
        = Space.pointsMapULift.{u + 1} B S hS Xred.obj (iX.hom ≫ f.hom) pt := by rw [hhom]
    simpa only [Space.pointsMapULift_comp, Function.comp_apply] using h₁
  constructor
  · intro hsurj pt
    obtain ⟨pre, hpre⟩ := hsurj (Space.pointsMapULift.{u + 1} B S hS Yred.obj iY.hom pt)
    obtain ⟨rpre, hrpre⟩ := hiX.bijective_pointsMapULift.2 pre
    refine ⟨rpre, hYbij.1 ?_⟩
    rw [hcomm, hrpre, hpre]
  · intro hsurj pt
    obtain ⟨rpt, hrpt⟩ := hYbij.2 pt
    obtain ⟨pre, hpre⟩ := hsurj rpt
    refine ⟨Space.pointsMapULift.{u + 1} B S hS Xred.obj iX.hom pre, ?_⟩
    rw [← hcomm, hpre, hrpt]

end AlgebraicGeometry.FormalSpace

end
