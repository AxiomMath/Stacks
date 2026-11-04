module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.ClosureProduct

/-!
# The closure of the image on arrows of a morphism of groupoid schemes over a field

For a morphism of groupoid schemes which is the identity on a common scheme of objects, and
when that scheme of objects is the spectrum of a field, the closure of the image on arrows is
stable under composition: if two composable arrows both lie in that closure, so does their
composite.

This is the step which lets one put a groupoid structure on the reduced closed subscheme
supported on the closure of the image.

## Main results

* `CategoryTheory.IsPullback.comp_isIso`: a cartesian square stays cartesian after composing
  both legs of its cospan with an isomorphism.
* `AlgebraicGeometry.comp_mapsTo_closure_range_mapArrows`: the composition morphism of the
  target groupoid maps the pairs of composable arrows lying in the closure of the image into
  that closure.

## Implementation notes

The statement is set theoretic, so no scheme structure on the closure is needed. The proof
compares the fibre product of the arrow schemes over the scheme of objects, taken in the over
category, with the fibre product of their underlying schemes over the spectrum of the field;
these agree because `CategoryTheory.Over.forget` preserves pullbacks and because composing the
legs of a cospan with one isomorphism does not change its fibre product. Over the field the
closure of the image of a product of morphisms is the product of the closures, which is the
content of Stacks 04Q0.

## References

* [Stacks Project, Tag 04Q7](https://stacks.math.columbia.edu/tag/04Q7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace CategoryTheory.IsPullback

/-- A cartesian square stays cartesian after composing both legs of its cospan with a single
isomorphism. -/
theorem comp_isIso {C : Type*} [Category C] {W X Y Z Z' : C} {fst : W ⟶ X} {snd : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : Z ⟶ Z') [IsIso e] :
    IsPullback fst snd (f ≫ e) (g ≫ e) := by
  simpa using
    h.paste_vert (IsPullback.of_vert_isIso (⟨by simp⟩ : CommSq g (𝟙 Y) e (g ≫ e)))

end CategoryTheory.IsPullback

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04Q7.** For a morphism of groupoid schemes over a field which is the
identity on the common scheme of objects, the closure of the image on arrows is stable under
composition. -/
@[stacks 04Q7]
theorem comp_mapsTo_closure_range_mapArrows {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects) (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects) :
    Set.MapsTo G₂.comp.left.base
      ((pullback.fst G₂.source G₂.target).left.base ⁻¹'
          closure (Set.range F.mapArrows.left.base) ∩
        (pullback.snd G₂.source G₂.target).left.base ⁻¹'
          closure (Set.range F.mapArrows.left.base))
      (closure (Set.range F.mapArrows.left.base)) := by
  have hfield₂ : G₂.objects.left = Spec (.of k) := by rw [← hobjects]; exact hfield
  let pA : G₁.arrows.left ⟶ Spec (.of k) := G₁.source.left ≫ eqToHom hfield
  let pB : G₁.arrows.left ⟶ Spec (.of k) := G₁.target.left ≫ eqToHom hfield
  let pX : G₂.arrows.left ⟶ Spec (.of k) := G₂.source.left ≫ eqToHom hfield₂
  let pY : G₂.arrows.left ⟶ Spec (.of k) := G₂.target.left ≫ eqToHom hfield₂
  have hmapObjects' : F.mapObjects.left ≫ eqToHom hfield₂ = eqToHom hfield := by
    rw [show F.mapObjects.left = (eqToHom hobjects).left from
      congrArg Over.Hom.left hmapObjects]
    simp
  have hsrc : F.mapArrows.left ≫ pX = pA := by
    change F.mapArrows.left ≫ G₂.source.left ≫ eqToHom hfield₂ =
      G₁.source.left ≫ eqToHom hfield
    rw [← Category.assoc, F.map_source_left, Category.assoc, hmapObjects']
  have htgt : F.mapArrows.left ≫ pY = pB := by
    change F.mapArrows.left ≫ G₂.target.left ≫ eqToHom hfield₂ =
      G₁.target.left ≫ eqToHom hfield
    rw [← Category.assoc, F.map_target_left, Category.assoc, hmapObjects']
  let i₁ : (pullback G₁.source G₁.target).left ≅ pullback pA pB :=
    ((overFibreProduct_isPullback G₁.source G₁.target).comp_isIso
      (eqToHom hfield)).isoPullback
  let i₂ : (pullback G₂.source G₂.target).left ≅ pullback pX pY :=
    ((overFibreProduct_isPullback G₂.source G₂.target).comp_isIso
      (eqToHom hfield₂)).isoPullback
  have hi₁fst : i₁.hom ≫ pullback.fst pA pB = (pullback.fst G₁.source G₁.target).left :=
    IsPullback.isoPullback_hom_fst _
  have hi₁snd : i₁.hom ≫ pullback.snd pA pB = (pullback.snd G₁.source G₁.target).left :=
    IsPullback.isoPullback_hom_snd _
  have hi₂fst : i₂.hom ≫ pullback.fst pX pY = (pullback.fst G₂.source G₂.target).left :=
    IsPullback.isoPullback_hom_fst _
  have hi₂snd : i₂.hom ≫ pullback.snd pX pY = (pullback.snd G₂.source G₂.target).left :=
    IsPullback.isoPullback_hom_snd _
  let m : pullback pA pB ⟶ pullback pX pY :=
    pullback.map pA pB pX pY F.mapArrows.left F.mapArrows.left (𝟙 _)
      (by simpa using hsrc.symm) (by simpa using htgt.symm)
  have hmfst : m ≫ pullback.fst pX pY = pullback.fst pA pB ≫ F.mapArrows.left :=
    pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd pX pY = pullback.snd pA pB ≫ F.mapArrows.left :=
    pullback.lift_snd _ _ _
  have hcfst : F.mapComposable ≫ pullback.fst G₂.source G₂.target =
      pullback.fst G₁.source G₁.target ≫ F.mapArrows := pullback.lift_fst _ _ _
  have hcsnd : F.mapComposable ≫ pullback.snd G₂.source G₂.target =
      pullback.snd G₁.source G₁.target ≫ F.mapArrows := pullback.lift_snd _ _ _
  have hcomm : i₁.hom ≫ m = F.mapComposable.left ≫ i₂.hom := by
    apply pullback.hom_ext
    · calc
        (i₁.hom ≫ m) ≫ pullback.fst pX pY =
            (pullback.fst G₁.source G₁.target).left ≫ F.mapArrows.left := by
              rw [Category.assoc, hmfst, ← Category.assoc, hi₁fst]
        _ = F.mapComposable.left ≫ (pullback.fst G₂.source G₂.target).left := by
              simpa only [Over.comp_left] using (congrArg Over.Hom.left hcfst).symm
        _ = _ := by rw [Category.assoc, hi₂fst]
    · calc
        (i₁.hom ≫ m) ≫ pullback.snd pX pY =
            (pullback.snd G₁.source G₁.target).left ≫ F.mapArrows.left := by
              rw [Category.assoc, hmsnd, ← Category.assoc, hi₁snd]
        _ = F.mapComposable.left ≫ (pullback.snd G₂.source G₂.target).left := by
              simpa only [Over.comp_left] using (congrArg Over.Hom.left hcsnd).symm
        _ = _ := by rw [Category.assoc, hi₂snd]
  have hprod := closure_range_pullback_map pA pB pX pY F.mapArrows.left F.mapArrows.left
    hsrc htgt
  let c : pullback pX pY ⟶ G₂.arrows.left := i₂.inv ≫ G₂.comp.left
  have himage : c.base '' Set.range m.base ⊆ Set.range F.mapArrows.left.base := by
    rintro y ⟨z, ⟨z₀, rfl⟩, rfl⟩
    refine ⟨G₁.comp.left.base (i₁.inv.base z₀), ?_⟩
    have hz : i₁.hom.base (i₁.inv.base z₀) = z₀ :=
      congrArg (fun f : pullback pA pB ⟶ pullback pA pB => f.base z₀) i₁.inv_hom_id
    have hpt : m.base z₀ = i₂.hom.base (F.mapComposable.left.base (i₁.inv.base z₀)) := by
      simpa [hz] using
        congrArg (fun f : (pullback G₁.source G₁.target).left ⟶ pullback pX pY =>
          f.base (i₁.inv.base z₀)) hcomm
    have hcomp : G₂.comp.left.base (F.mapComposable.left.base (i₁.inv.base z₀)) =
        F.mapArrows.left.base (G₁.comp.left.base (i₁.inv.base z₀)) := by
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
        congrArg (fun f : (pullback G₁.source G₁.target).left ⟶ G₂.arrows.left =>
          f.base (i₁.inv.base z₀)) (congrArg Over.Hom.left F.comp_mapArrows.symm)
    rw [hpt]
    change _ = (i₂.hom ≫ i₂.inv ≫ G₂.comp.left).base _
    simpa only [Iso.hom_inv_id_assoc] using hcomp.symm
  intro x hx
  have hmem : i₂.hom.base x ∈ closure (Set.range m.base) := by
    rw [← hprod]
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, hi₂fst] using hx.1
    · simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, hi₂snd] using hx.2
  have hresult := ((image_closure_subset_closure_image c.continuous).trans
    (closure_mono himage)) ⟨i₂.hom.base x, hmem, rfl⟩
  have hcancel : c.base (i₂.hom.base x) = G₂.comp.left.base x := by
    change (i₂.hom ≫ i₂.inv ≫ G₂.comp.left).base x = _
    simp
  rwa [hcancel] at hresult

end AlgebraicGeometry

end
