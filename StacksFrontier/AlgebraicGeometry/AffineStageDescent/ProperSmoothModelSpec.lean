module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel

/-!
# A proper smooth morphism to an affine scheme comes from a Noetherian ring

The model of `StacksFrontier/AlgebraicGeometry/AffineStageDescent/ProperSmoothModel.lean` lives over
the spectrum of a finitely generated subring of `Γ(S, ⊤)`. This file records that form of the
conclusion: the Noetherian base of the model is `Spec A` for a Noetherian ring `A`, which is the
shape the commutative-algebra statements about a proper family over an affine base are made in.

## Main results

* `AlgebraicGeometry.exists_isPullback_spec_isNoetherianRing_properSmooth`: the model over
  `Spec A`, `A` Noetherian.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A proper smooth morphism to an affine scheme is the base change of a proper smooth
morphism to the spectrum of a Noetherian ring.** -/
theorem exists_isPullback_spec_isNoetherianRing_properSmooth {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] [Smooth f] :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (Y : Scheme.{u})
      (h : Y ⟶ Spec (.of A)) (q : S ⟶ Spec (.of A)) (q' : X ⟶ Y),
      IsProper h ∧ Smooth h ∧ IsPullback q' f h q := by
  let D := specAdjoinFinsetDiagram Γ(S, ⊤)
  let c := affineStageCone S
  have hc : IsLimit c := isLimit_affineStageCone S
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let f' : X ⟶ c.pt := f
  have : IsProper f' := ‹IsProper f›
  have : Flat f' := inferInstanceAs (Flat f)
  obtain ⟨i, X₁, f₁, g₁, hpr₁, hfl₁, hfp₁, hpb₁⟩ :=
    exists_stage_properFlatModel D c hc f' hfp
  have : LocallyOfFinitePresentation f₁ := hfp₁.1
  have : QuasiCompact f₁ := hfp₁.2.1
  have : QuasiSeparated f₁ := hfp₁.2.2
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let X₀ : Over (D.obj i) := Over.mk f₁
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace X₁)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace X₁)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  have key : ∀ {T : Scheme.{u}} (b : T ⟶ D.obj i),
      Smooth ((Over.pullback b).map a).left ↔ Smooth (pullback.snd f₁ b) := by
    intro T b
    have hw : ((Over.pullback b).map a).left ≫ pullback.snd (𝟙 (D.obj i)) b =
        pullback.snd f₁ b := Over.w ((Over.pullback b).map a)
    rw [← hw]
    exact (MorphismProperty.cancel_right_of_respectsIso (@Smooth.{u}) _ _).symm
  have hsm : Smooth ((Over.pullback (c.π.app i)).map a).left := by
    rw [key, ← MorphismProperty.cancel_left_of_respectsIso (@Smooth.{u}) hpb₁.isoPullback.hom,
      hpb₁.isoPullback_hom_snd]
    exact inferInstanceAs (Smooth f)
  obtain ⟨j, k, hj⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i X₀ Y₀ a hc
  rw [key] at hj
  have hsq : IsPullback (pullback.fst f₁ (D.map k)) (pullback.snd f₁ (D.map k)) f₁ (D.map k) :=
    IsPullback.of_hasPullback f₁ (D.map k)
  have hcond : g₁ ≫ f₁ = (f' ≫ c.π.app j) ≫ D.map k := by
    rw [hpb₁.w, Category.assoc, c.w k]
  have hpb : IsPullback (pullback.lift g₁ (f' ≫ c.π.app j) hcond) f'
      (pullback.snd f₁ (D.map k)) (c.π.app j) :=
    IsPullback.of_right (by rwa [pullback.lift_fst, c.w k]) (pullback.lift_snd _ _ _) hsq
  exact ⟨Algebra.adjoin ℤ ((j.unop : Finset Γ(S, ⊤)) : Set Γ(S, ⊤)), inferInstance,
    isNoetherianRing_adjoinFinset_int Γ(S, ⊤) j.unop, pullback f₁ (D.map k),
    pullback.snd f₁ (D.map k), c.π.app j, pullback.lift g₁ (f' ≫ c.π.app j) hcond,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hsq hpr₁, hj, hpb⟩

end AlgebraicGeometry

end
