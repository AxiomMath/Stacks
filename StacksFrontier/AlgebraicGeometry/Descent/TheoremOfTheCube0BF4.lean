module

public import StacksFrontier.AlgebraicGeometry.Descent.TheoremOfTheCube
public import StacksFrontier.AlgebraicGeometry.Descent.CubeTrivialGlue

/-!
# The theorem of the cube, under the hypotheses of the source

[Stacks, Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4): let `S` be a scheme, let `X`, `Y`
and `Z` be schemes over `S` with sections `x : S ⟶ X` and `y : S ⟶ Y` of the structure morphisms,
and let `L` be an invertible module on `X ×_S Y ×_S Z`. If `X ⟶ S` and `Y ⟶ S` are flat, proper,
of finite presentation with geometrically integral fibres, the pullbacks of `L` along
`x × 1 × 1` and `1 × y × 1` are trivial, the restriction of `L` to one fibre `X ×_S Y ×_S z` is
trivial, and `Z` is connected, then `L` is trivial.

The spellings are those of `AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_face_and_fiber`
in `StacksFrontier/AlgebraicGeometry/Descent/TheoremOfTheCube.lean`. The proof writes the projection
`p : X ×_S Y ×_S Z ⟶ Z` as the product `(X ×_S Z) ×_Z (Y ×_S Z) ⟶ Z`, as the source does, and
applies `Stacks.Cube.nonempty_iso_unit`, the theorem over an arbitrary connected base.

## Main results

* `AlgebraicGeometry.SheafOfModules.isTrivial_of_isTrivial_faces_and_fiber`: Tag 0BF4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

namespace SheafOfModules

/-- **The theorem of the cube.** Let `f : X ⟶ S`, `g : Y ⟶ S` and `h : Z ⟶ S` be morphisms of
schemes, with `f` and `g` flat, proper, of finite presentation and with geometrically integral
fibres, let `x` and `y` be sections of `f` and `g`, and let `L` be an invertible module on
`X ×_S Y ×_S Z` whose pullbacks along the faces `x × 1 × 1` and `1 × y × 1` are trivial and whose
restriction to one fibre `X ×_S Y ×_S z` is trivial. If `Z` is connected, then `L` is trivial.

The fibre over `z` is the base change of the projection `X ×_S Y ×_S Z ⟶ Z` along
`Z.fromSpecResidueField z`. -/
@[stacks 0BF4]
theorem isTrivial_of_isTrivial_faces_and_fiber {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (x : S ⟶ X) (hx : x ≫ f = 𝟙 S) (y : S ⟶ Y) (hy : y ≫ g = 𝟙 S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f) [GeometricallyIntegral f]
    [Flat g] [IsProper g] (hgp : FinitePresentation g) [GeometricallyIntegral g]
    [ConnectedSpace Z]
    (L : _root_.SheafOfModules.{u}
      (structureSheafRing (pullback (pullback.fst f g ≫ f) h).toRingedSpace))
    [IsInvertible (pullback (pullback.fst f g ≫ f) h).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.fst f g ≫ f) h).IsSheaf) L]
    (hfaceX :
      let i : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
        pullback.lift
          (pullback.lift (pullback.fst g h ≫ g ≫ x) (pullback.fst g h)
            (by simp only [Category.assoc, hx, Category.comp_id]))
          (pullback.snd g h)
          (by rw [pullback.lift_fst_assoc]
              simp only [Category.assoc, hx, Category.comp_id, pullback.condition])
      IsTrivial (pullback g h).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback g h).IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfaceY :
      let i : pullback f h ⟶ pullback (pullback.fst f g ≫ f) h :=
        pullback.lift
          (pullback.lift (pullback.fst f h) (pullback.fst f h ≫ f ≫ y)
            (by simp only [Category.assoc, hy, Category.comp_id]))
          (pullback.snd f h)
          (by rw [pullback.lift_fst_assoc, pullback.condition])
      IsTrivial (pullback f h).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback f h).IsSheaf)
        ((modulePullback i.toLRSHom.toShHom).obj L))
    (hfiber : ∃ z : Z,
      IsTrivial (pullback (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback (pullback.snd (pullback.fst f g ≫ f) h)
            (Z.fromSpecResidueField z)).IsSheaf)
        ((modulePullback (pullback.fst (pullback.snd (pullback.fst f g ≫ f) h)
          (Z.fromSpecResidueField z)).toLRSHom.toShHom).obj L)) :
    IsTrivial (pullback (pullback.fst f g ≫ f) h).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (pullback.fst f g ≫ f) h).IsSheaf) L := by
  have := hfp.locallyOfFinitePresentation
  have := hgp.locallyOfFinitePresentation
  have : Stacks.SheafOfModules.IsInvertible (pullback (pullback.fst f g ≫ f) h).presheaf
      (pullback (pullback.fst f g ≫ f) h).ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry (h := ‹_›)
  -- `X ×_S Y ×_S Z` as the fibre product `(X ×_S Z) ×_Z (Y ×_S Z)`
  let r : pullback (pullback.fst f g ≫ f) h ⟶ pullback f h :=
    pullback.lift (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g)
      (pullback.snd (pullback.fst f g ≫ f) h) (by rw [Category.assoc]; exact pullback.condition)
  let q : pullback (pullback.fst f g ≫ f) h ⟶ pullback g h :=
    pullback.lift (pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.snd f g)
      (pullback.snd (pullback.fst f g ≫ f) h)
      (by rw [Category.assoc, ← pullback.condition (f := f) (g := g)]; exact pullback.condition)
  have hq1 : q ≫ pullback.snd g h = pullback.snd (pullback.fst f g ≫ f) h :=
    pullback.lift_snd _ _ _
  have hq2 : q ≫ pullback.fst g h =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.snd f g := pullback.lift_fst _ _ _
  have hr1 : r ≫ pullback.snd f h = pullback.snd (pullback.fst f g ≫ f) h :=
    pullback.lift_snd _ _ _
  have hr2 : r ≫ pullback.fst f h =
      pullback.fst (pullback.fst f g ≫ f) h ≫ pullback.fst f g := pullback.lift_fst _ _ _
  have s' : IsPullback (q ≫ pullback.snd g h) (pullback.fst (pullback.fst f g ≫ f) h) h
      (pullback.snd f g ≫ g) := by
    rw [hq1, ← pullback.condition (f := f) (g := g)]
    exact (IsPullback.of_hasPullback _ _).flip
  have sTop : IsPullback q (pullback.fst (pullback.fst f g ≫ f) h) (pullback.fst g h)
      (pullback.snd f g) :=
    IsPullback.of_right s' hq2 (IsPullback.of_hasPullback g h).flip
  have sOuter : IsPullback (r ≫ pullback.fst f h) q f (pullback.snd g h ≫ h) := by
    rw [hr2, ← pullback.condition (f := g) (g := h)]
    exact (sTop.paste_vert (IsPullback.of_hasPullback f g).flip).flip
  have H : IsPullback r q (pullback.snd f h) (pullback.snd g h) :=
    IsPullback.of_right sOuter (hr1.trans hq1.symm) (IsPullback.of_hasPullback f h)
  -- the sections and the faces
  let σ : Z ⟶ pullback f h := pullback.lift (h ≫ x) (𝟙 Z)
    (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  let τ : Z ⟶ pullback g h := pullback.lift (h ≫ y) (𝟙 Z)
    (by rw [Category.assoc, hy, Category.comp_id, Category.id_comp])
  let j₁ : pullback g h ⟶ pullback (pullback.fst f g ≫ f) h :=
    pullback.lift
      (pullback.lift (pullback.fst g h ≫ g ≫ x) (pullback.fst g h)
        (by simp only [Category.assoc, hx, Category.comp_id]))
      (pullback.snd g h)
      (by rw [pullback.lift_fst_assoc]
          simp only [Category.assoc, hx, Category.comp_id, pullback.condition])
  let j₂ : pullback f h ⟶ pullback (pullback.fst f g ≫ f) h :=
    pullback.lift
      (pullback.lift (pullback.fst f h) (pullback.fst f h ≫ f ≫ y)
        (by simp only [Category.assoc, hy, Category.comp_id]))
      (pullback.snd f h)
      (by rw [pullback.lift_fst_assoc, pullback.condition])
  have hσ : σ ≫ pullback.snd f h = 𝟙 Z := pullback.lift_snd _ _ _
  have hτ : τ ≫ pullback.snd g h = 𝟙 Z := pullback.lift_snd _ _ _
  have hj₁r : j₁ ≫ r = pullback.snd g h ≫ σ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr2, Category.assoc]
      dsimp only [j₁, σ]
      rw [pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst, pullback.condition_assoc]
    · rw [Category.assoc, hr1, Category.assoc]
      dsimp only [j₁, σ]
      rw [pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have hj₁q : j₁ ≫ q = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq2, Category.id_comp]
      dsimp only [j₁]
      rw [pullback.lift_fst_assoc, pullback.lift_snd]
    · rw [Category.assoc, hq1, Category.id_comp]
      dsimp only [j₁]
      rw [pullback.lift_snd]
  have hj₂r : j₂ ≫ r = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr2, Category.id_comp]
      dsimp only [j₂]
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hr1, Category.id_comp]
      dsimp only [j₂]
      rw [pullback.lift_snd]
  have hj₂q : j₂ ≫ q = pullback.snd f h ≫ τ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hq2, Category.assoc]
      dsimp only [j₂, τ]
      rw [pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst, pullback.condition_assoc]
    · rw [Category.assoc, hq1, Category.assoc]
      dsimp only [j₂, τ]
      rw [pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  obtain ⟨z₀, hz₀⟩ := hfiber
  exact Stacks.Cube.nonempty_iso_unit H σ τ hσ hτ j₁ hj₁r hj₁q j₂ hj₂r hj₂q L hfaceX hfaceY
    (pullback.snd (pullback.fst f g ≫ f) h) hr1 z₀ hz₀

end SheafOfModules

end AlgebraicGeometry

end
