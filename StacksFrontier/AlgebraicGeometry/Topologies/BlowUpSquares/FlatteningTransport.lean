module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Flattening

/-!
# The diagram of Stacks tag 0EVC along an abstract base change

`AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.baseChange` transports the conclusion of Stacks
tag 0EVC along the projection `W ×_Y X ⟶ W` of a literal fibre product. A base change met in
practice is not that morphism but one which is only *cartesian* over it: the model `X_i ⟶ Y_i` of
a scheme of finite presentation over an inverse limit `Y = lim Y_i` is produced by Stacks tag
01ZM, part (1) as a pullback square rather than as a fibre product. This module records the
transport of the tag's conclusion along an isomorphism of the source; the form of the base change
which consumes such a square is `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.of_isPullback`.

## Main results

* `AlgebraicGeometry.isAlmostBlowUpSquare_comp_isoInv`: an almost blowup square transported along
  an isomorphism of its base.
* `AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.of_iso`: the conclusion of Stacks tag 0EVC
  only depends on the source of the morphism up to isomorphism over the base.

## Implementation notes

The transport of an almost blowup square along an isomorphism `e : X₂ ≅ X₁` of its base is not a
new computation: it is the base change of the square along `e.hom`, which is
`AlgebraicGeometry.isAlmostBlowUpSquare_baseChange` (tag 0EV7), read through the isomorphism
`X' ≅ X₂ ×_{X₁} X'` which identifies the base-changed modification with `b ≫ e.inv`. That
isomorphism is the lift of `b ≫ e.inv` and the identity, inverse to the second projection, and
precomposing a modification with it leaves the square almost blowup by
`AlgebraicGeometry.isAlmostBlowUpSquare_isIso_comp`.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **The diagram of Stacks Project, Tag 0EVC base changes.** The conclusion of the tag is stable
under an arbitrary base change `p : W ⟶ Y`: the centre, both modifications and the relative
morphism of the diagram all base change, and the base-changed centre still misses the inverse
image of `V`.

This is the last step of the Stacks proof, where the diagram built over a Noetherian
approximation `Y_i` of `Y` is pulled back along `Y ⟶ Y_i`. Both almost blowup squares base change
by `AlgebraicGeometry.isAlmostBlowUpSquare_baseChange` (tag 0EV7), the two centres staying
inverse images of one another because the two routes `W ×_Y X ⟶ Y` agree. The relative morphism
base changes because `W ×_Y X'` is `(W ×_Y Y') ×_{Y'} X'`, which is what the horizontal pasting
of the two defining squares says; flatness and finite presentation are then inherited by base
change. -/
public theorem HasFlatAlmostBlowUpSquarePair.baseChange {W : Scheme.{u}} {f : X ⟶ Y}
    {V : Y.Opens} (H : HasFlatAlmostBlowUpSquarePair f V) (p : W ⟶ Y) :
    HasFlatAlmostBlowUpSquarePair (pullback.fst p f) (p ⁻¹ᵁ V) := by
  obtain ⟨Z, Y', b, X', c, g, hleft, hright, hdisj, hcomm, hflat, hfp⟩ := H
  have hsq₁ : IsPullback (pullback.fst (pullback.snd p f) c) (pullback.snd (pullback.snd p f) c)
      (pullback.snd p f) c := IsPullback.of_hasPullback _ _
  have hsq₂ : IsPullback (pullback.fst p f) (pullback.snd p f) p f := IsPullback.of_hasPullback _ _
  have hsq₃ : IsPullback (pullback.fst p b) (pullback.snd p b) p b := IsPullback.of_hasPullback _ _
  have hZ : (Z.comap p).comap (pullback.fst p f) = (Z.comap f).comap (pullback.snd p f) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq₂.w]
  have hlift : (pullback.fst (pullback.snd p f) c ≫ pullback.fst p f) ≫ p =
      (pullback.snd (pullback.snd p f) c ≫ g) ≫ b := by
    calc (pullback.fst (pullback.snd p f) c ≫ pullback.fst p f) ≫ p
        = pullback.fst (pullback.snd p f) c ≫ pullback.snd p f ≫ f := by
          rw [Category.assoc, hsq₂.w]
      _ = (pullback.snd (pullback.snd p f) c ≫ c) ≫ f := by rw [← Category.assoc, hsq₁.w]
      _ = pullback.snd (pullback.snd p f) c ≫ g ≫ b := by
          rw [Category.assoc, hcomm]
      _ = (pullback.snd (pullback.snd p f) c ≫ g) ≫ b := (Category.assoc _ _ _).symm
  have hsq : IsPullback
      (pullback.lift (pullback.fst (pullback.snd p f) c ≫ pullback.fst p f)
        (pullback.snd (pullback.snd p f) c ≫ g) hlift)
      (pullback.snd (pullback.snd p f) c) (pullback.snd p b) g :=
    IsPullback.of_right (by
      rw [pullback.lift_fst, hcomm]; exact hsq₁.paste_horiz hsq₂)
      (pullback.lift_snd _ _ _) hsq₃
  refine ⟨Z.comap p, pullback p b, pullback.fst p b, pullback (pullback.snd p f) c,
    pullback.fst (pullback.snd p f) c, _, isAlmostBlowUpSquare_baseChange Z b p hleft, ?_, ?_,
    pullback.lift_fst _ _ _,
    MorphismProperty.of_isPullback (P := @Flat) hsq.flip hflat,
    ⟨MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq.flip hfp.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hfp.2.1,
      MorphismProperty.of_isPullback (P := @QuasiSeparated) hsq.flip hfp.2.2⟩⟩
  · rw [hZ]
    exact isAlmostBlowUpSquare_baseChange (Z.comap f) c (pullback.snd p f) hright
  · have hsupp : (((Z.comap p).support) : Set W) = p.base ⁻¹' (Z.support : Set Y) := by
      rw [Scheme.IdealSheafData.support_comap]; rfl
    rw [hsupp]
    exact hdisj.preimage p.base

/-- **An almost blowup square transported along an isomorphism of its base.** If `b` is the
modification of an almost blowup square with centre `I` on `X₁` and `e : X₂ ≅ X₁` is an
isomorphism, then `b ≫ e.inv` is the modification of an almost blowup square with centre
`I·𝒪_{X₂}`.

This is the base change of the square along `e.hom`, read through the isomorphism
`X' ≅ X₂ ×_{X₁} X'` which carries the base-changed modification to `b ≫ e.inv`. -/
public theorem isAlmostBlowUpSquare_comp_isoInv {X₁ X₂ X' : Scheme.{u}} (I : X₁.IdealSheafData)
    {b : X' ⟶ X₁} (h : IsAlmostBlowUpSquare I b) (e : X₂ ≅ X₁) :
    IsAlmostBlowUpSquare (I.comap e.hom) (b ≫ e.inv) := by
  have hcond : (b ≫ e.inv) ≫ e.hom = 𝟙 X' ≫ b := by simp
  have hsnd : pullback.lift (b ≫ e.inv) (𝟙 X') hcond ≫ pullback.snd e.hom b = 𝟙 X' :=
    pullback.lift_snd _ _ _
  have hc : pullback.fst e.hom b ≫ e.hom = pullback.snd e.hom b ≫ b := pullback.condition
  have hiso : IsIso (pullback.lift (b ≫ e.inv) (𝟙 X') hcond) :=
    ⟨pullback.snd e.hom b, hsnd, by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        rw [← Category.assoc, ← hc, Category.assoc, e.hom_inv_id, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]⟩
  have hbc := isAlmostBlowUpSquare_isIso_comp (I.comap e.hom)
    (isAlmostBlowUpSquare_baseChange I b e.hom h) (pullback.lift (b ≫ e.inv) (𝟙 X') hcond)
  rwa [pullback.lift_fst] at hbc

/-- **The conclusion of Stacks Project, Tag 0EVC depends on the source only up to isomorphism.**
If `e : X₂ ≅ X₁` is an isomorphism over `Y`, carrying `f₂` to `f₁`, then the diagram of the tag
for `f₁` and `V` gives one for `f₂` and `V`: the centre on the base, both modifications and the
relative morphism are unchanged, and only the right-hand modification is read through `e`. -/
public theorem HasFlatAlmostBlowUpSquarePair.of_iso {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ Y}
    {V : Y.Opens} (H : HasFlatAlmostBlowUpSquarePair f₁ V) {f₂ : X₂ ⟶ Y} (e : X₂ ≅ X₁)
    (he : e.hom ≫ f₁ = f₂) : HasFlatAlmostBlowUpSquarePair f₂ V := by
  obtain ⟨Z, Y', b, X', c, g, hleft, hright, hdisj, hcomm, hflat, hfp⟩ := H
  refine ⟨Z, Y', b, X', c ≫ e.inv, g, hleft, ?_, hdisj, ?_, hflat, hfp⟩
  · have hZ : Z.comap f₂ = (Z.comap f₁).comap e.hom := by
      rw [← he, Scheme.IdealSheafData.comap_comp]
    rw [hZ]
    exact isAlmostBlowUpSquare_comp_isoInv (Z.comap f₁) hright e
  · rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hcomm

end AlgebraicGeometry

end
