module

public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.SeparatedTwoOpens
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBase

/-!
# Finite type and separatedness of a scheme glued from two opens over a base

Two schemes `Y₁` and `Y₂` with a common open subscheme `W`, presented as a span `Y₁ ⟵ W ⟶ Y₂`
of open immersions, glue to a scheme `AlgebraicGeometry.SpanGlue.glued`. If both pieces are of
finite type over a base `T` then so is the glueing, and if both pieces are separated over `T`
*and* the common open is closed in `Y₁ ×_T Y₂`, then the glueing is separated over `T`.

## Main results

* `AlgebraicGeometry.isSeparated_of_isOpenImmersion_cover`: a morphism whose source is covered by
  the images of two open immersions, each separated over the base and with closed intersection
  in their fibre product over the base, is separated.
* `AlgebraicGeometry.SpanGlue.compactSpace_glued`: the glueing of two quasi-compact schemes is
  quasi-compact.
* `AlgebraicGeometry.SpanGlue.isPullback_ι`: the two charts meet exactly in `W`, as a cartesian
  square.
* `AlgebraicGeometry.SpanGlue.locallyOfFiniteType_desc`: the glueing is locally of finite type
  over the base as soon as both pieces are.
* `AlgebraicGeometry.SpanGlue.isSeparated_desc`: **the glueing is separated over the base** as
  soon as both pieces are and the common open is closed in the fibre product of the pieces.

## References

* [Stacks Project, Tag 0F3U](https://stacks.math.columbia.edu/tag/0F3U)
* [Stacks Project, Tag 0F3X](https://stacks.math.columbia.edu/tag/0F3X)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism is separated as soon as its source is covered by the images of two open immersions
which are separated over the base and whose fibre product over the base contains their intersection
as a closed subscheme. -/
theorem isSeparated_of_isOpenImmersion_cover {X S A B : Scheme.{u}} (f : X ⟶ S)
    (a : A ⟶ X) (b : B ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
    (hcover : a.opensRange ⊔ b.opensRange = ⊤)
    [IsSeparated (a ≫ f)] [IsSeparated (b ≫ f)]
    (hab : IsClosedImmersion (pullback.mapDesc a b f)) : IsSeparated f := by
  have ha : a.isoOpensRange.hom ≫ a.opensRange.ι = a := Scheme.Hom.isoOpensRange_hom_ι a
  have hb : b.isoOpensRange.hom ≫ b.opensRange.ι = b := Scheme.Hom.isoOpensRange_hom_ι b
  have hs : ∀ {C : Scheme.{u}} (c : C ⟶ X) [IsOpenImmersion c] [IsSeparated (c ≫ f)],
      IsSeparated (c.opensRange.ι ≫ f) := by
    intro C c _ _
    have e : c.opensRange.ι ≫ f = c.isoOpensRange.inv ≫ c ≫ f := by simp
    rw [e]; infer_instance
  have hsa := hs a
  have hsb := hs b
  refine isSeparated_of_sup_eq_top_of_isClosedImmersion_mapDesc f a.opensRange b.opensRange
    hcover ?_
  set L := pullback.map a b a.opensRange.ι b.opensRange.ι
    a.isoOpensRange.hom b.isoOpensRange.hom (𝟙 X) (by simp [ha]) (by simp [hb]) with hL
  set R := pullback.map (a ≫ f) (b ≫ f) (a.opensRange.ι ≫ f) (b.opensRange.ι ≫ f)
    a.isoOpensRange.hom b.isoOpensRange.hom (𝟙 S)
    (by rw [Category.comp_id, ← Category.assoc, ha]) (by
      rw [Category.comp_id, ← Category.assoc, hb]) with hR
  have hLiso : IsIso L := by rw [hL]; infer_instance
  have hRiso : IsIso R := by rw [hR]; infer_instance
  have hcomm : L ≫ pullback.mapDesc a.opensRange.ι b.opensRange.ι f =
      pullback.mapDesc a b f ≫ R := by
    apply pullback.hom_ext <;>
      simp [hL, hR, pullback.mapDesc, pullback.map]
  have hiso : Arrow.mk (pullback.mapDesc a b f) ≅
      Arrow.mk (pullback.mapDesc a.opensRange.ι b.opensRange.ι f) :=
    Arrow.isoMk (asIso L) (asIso R) (by simpa using hcomm)
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) hiso).mp hab

namespace SpanGlue

variable {W Y₁ Y₂ : Scheme.{u}} (j₁ : W ⟶ Y₁) (j₂ : W ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- The glueing of two quasi-compact schemes along a common open subscheme is quasi-compact. -/
theorem compactSpace_glued [CompactSpace Y₁] [CompactSpace Y₂] :
    CompactSpace (glued j₁ j₂) := by
  rw [← isCompact_univ_iff]
  have he : (Set.univ : Set (glued j₁ j₂)) =
      Set.range (ι₁ j₁ j₂).base ∪ Set.range (ι₂ j₁ j₂).base := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    exact ι_jointly_surjective j₁ j₂ x
  rw [he]
  exact (isCompact_range (ι₁ j₁ j₂).continuous).union (isCompact_range (ι₂ j₁ j₂).continuous)

/-- **The two charts of the glueing meet exactly in the common open subscheme**, as a cartesian
square. -/
theorem isPullback_ι : IsPullback j₁ j₂ (ι₁ j₁ j₂) (ι₂ j₁ j₂) :=
  IsOpenImmersion.isPullback j₁ j₂ (ι₁ j₁ j₂) (ι₂ j₁ j₂) (glue_condition j₁ j₂).symm
    (preimage_opensRange_ι₁ j₁ j₂)

variable {T : Scheme.{u}} (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (h : j₁ ≫ g₁ = j₂ ≫ g₂)

/-- **The glued scheme is locally of finite type over the base** as soon as both pieces are. -/
theorem locallyOfFiniteType_desc [LocallyOfFiniteType g₁] [LocallyOfFiniteType g₂] :
    LocallyOfFiniteType (desc j₁ j₂ g₁ g₂ h) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have key : ∀ i : WidePushoutShape Bool,
      LocallyOfFiniteType (colimit.ι (diagram j₁ j₂) i ≫ desc j₁ j₂ g₁ g₂ h) := by
    intro i
    have e : colimit.ι (diagram j₁ j₂) i ≫ desc j₁ j₂ g₁ g₂ h =
        (cocone j₁ j₂ g₁ g₂ h).ι.app i :=
      colimit.ι_desc (cocone j₁ j₂ g₁ g₂ h) i
    rw [e]
    match i with
    | none => exact inferInstanceAs (LocallyOfFiniteType (j₁ ≫ g₁))
    | some false => exact inferInstanceAs (LocallyOfFiniteType g₁)
    | some true => exact inferInstanceAs (LocallyOfFiniteType g₂)
  exact IsZariskiLocalAtSource.of_openCover (openCover j₁ j₂) fun i => key i

/-- **The glued scheme is separated over the base** as soon as both pieces are and the common
open subscheme is closed in the fibre product of the two pieces over the base. -/
theorem isSeparated_desc [IsSeparated g₁] [IsSeparated g₂]
    (hcross : IsClosedImmersion (pullback.lift j₁ j₂ h)) :
    IsSeparated (desc j₁ j₂ g₁ g₂ h) := by
  have hd₁ : ι₁ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h = g₁ := ι₁_desc j₁ j₂ g₁ g₂ h
  have hd₂ : ι₂ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h = g₂ := ι₂_desc j₁ j₂ g₁ g₂ h
  have hs₁ : IsSeparated (ι₁ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h) := by rw [hd₁]; infer_instance
  have hs₂ : IsSeparated (ι₂ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h) := by rw [hd₂]; infer_instance
  refine isSeparated_of_isOpenImmersion_cover (desc j₁ j₂ g₁ g₂ h) (ι₁ j₁ j₂) (ι₂ j₁ j₂)
    (opensRange_ι₁_sup_opensRange_ι₂ j₁ j₂) ?_
  have hp : IsPullback j₁ j₂ (ι₁ j₁ j₂) (ι₂ j₁ j₂) := isPullback_ι j₁ j₂
  have hw : j₁ ≫ (ι₁ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h) = j₂ ≫ (ι₂ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h) := by
    rw [hd₁, hd₂]; exact h
  have hfac : hp.isoPullback.hom ≫
      pullback.mapDesc (ι₁ j₁ j₂) (ι₂ j₁ j₂) (desc j₁ j₂ g₁ g₂ h) =
      pullback.lift j₁ j₂ hw := by
    apply pullback.hom_ext <;>
      simp [pullback.mapDesc, pullback.map]
  have hlift : IsClosedImmersion (pullback.lift j₁ j₂ hw) := by
    have e : Arrow.mk (pullback.lift (f := ι₁ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h)
        (g := ι₂ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h) j₁ j₂ hw) ≅
        Arrow.mk (pullback.lift j₁ j₂ h) :=
      Arrow.isoMk (Iso.refl W) (pullback.congrHom hd₁ hd₂) (by
        apply pullback.hom_ext <;>
          simp [pullback.congrHom, pullback.map])
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).mpr hcross
  rw [← hfac] at hlift
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hp.isoPullback.hom _).1 hlift

end SpanGlue

end AlgebraicGeometry

end
