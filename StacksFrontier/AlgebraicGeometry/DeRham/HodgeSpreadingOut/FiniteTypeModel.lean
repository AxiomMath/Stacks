module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.ProperSmoothModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A proper smooth scheme over a field comes from a finitely generated subring

Let `k` be a field and let `f : X ⟶ Spec k` be proper and smooth. Then there are a finitely
generated `ℤ`-algebra `R`, an injective ring map `R ⟶ k` and a proper smooth morphism
`Y ⟶ Spec R` whose base change to `Spec k` is `f`. This is the first step of the spreading out
argument in the proof of the degeneration of the Hodge-to-de Rham spectral sequence in
characteristic zero: `R` is the finitely generated subring of `k` at which the model of
`AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth` lives, and this file records that
ring instead of forgetting it.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_affineStageCone_properSmooth`: over an
  affine base `S`, the proper smooth model lives at a stage of the system of the spectra of the
  finitely generated subalgebras of `Γ(S, ⊤)`.
* `AlgebraicGeometry.HodgeSpreadingOut.exists_isPullback_finiteType_properSmooth`: over the
  spectrum of a ring `A` (a field, in the application), the model lives over the spectrum of a
  finitely generated `ℤ`-algebra mapping injectively to `A`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

/-- **A proper smooth morphism to an affine scheme `S` is the base change of a proper smooth
morphism to a stage of the system of the spectra of the finitely generated subalgebras of
`Γ(S, ⊤)`.** This is `AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth` with the
stage recorded. -/
@[ega "IV 17.7.9" "special case"]
theorem exists_isPullback_affineStageCone_properSmooth {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] [Smooth f] :
    ∃ (j : (Finset Γ(S, ⊤))ᵒᵖ) (Y : Scheme.{u}) (h : Y ⟶ (specAdjoinFinsetDiagram Γ(S, ⊤)).obj j)
      (q' : X ⟶ Y), IsProper h ∧ Smooth h ∧ IsPullback q' f h ((affineStageCone S).π.app j) := by
  let D := specAdjoinFinsetDiagram Γ(S, ⊤)
  let c := affineStageCone S
  have hc : IsLimit c := isLimit_affineStageCone S
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let f' : X ⟶ c.pt := f
  have : IsProper f' := ‹IsProper f›
  have : Flat f' := inferInstanceAs (Flat f)
  obtain ⟨i, X₁, f₁, g₁, hpr₁, hfl₁, hfp₁, hpb₁⟩ :=
    exists_stage_properFlatModel D c hc f' hfp
  obtain ⟨_, _, _⟩ := hfp₁
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
      (pullback.snd f₁ (D.map k)) (c.π.app j) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hsq
    rwa [pullback.lift_fst, c.w k]
  exact ⟨j, pullback f₁ (D.map k), pullback.snd f₁ (D.map k),
    pullback.lift g₁ (f' ≫ c.π.app j) hcond,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hsq hpr₁, hj, hpb⟩

/-- The stage morphism `Spec k ⟶ Spec ℤ[i]` of the affine stage cone of `Spec k` is the spectrum
of the inclusion `ℤ[i] ⟶ Γ(Spec k, ⊤)` followed by `Γ(Spec k, ⊤) ≅ k`. -/
theorem affineStageCone_π_app_spec (A : CommRingCat.{u}) (j : (Finset Γ(Spec A, ⊤))ᵒᵖ) :
    (affineStageCone (Spec A)).π.app j =
      Spec.map (CommRingCat.ofHom
          (Algebra.adjoin ℤ ((j.unop : Finset Γ(Spec A, ⊤)) : Set Γ(Spec A, ⊤))).val.toRingHom ≫
        (Scheme.ΓSpecIso A).hom) := by
  show (Spec A).isoSpec.hom ≫ (specAdjoinFinsetCone Γ(Spec A, ⊤)).π.app j = _
  rw [Scheme.isoSpec_Spec_hom, Spec.map_comp]
  rfl

/-- **A proper smooth scheme over a ring is the base change of a proper smooth scheme over a
finitely generated `ℤ`-algebra mapping injectively to the ring.** For `f : X ⟶ Spec A` proper and
smooth there are a finitely generated `ℤ`-algebra `R`, an injective ring map `φ : R ⟶ A` and a
proper smooth `h : Y ⟶ Spec R` with `X = Y ×_{Spec R} Spec A`. The ring `R` is the subring of
`Γ(Spec A, ⊤) ≅ A` generated by a finite set. -/
@[ega "IV 8.9.1" "(i), special case"]
theorem exists_isPullback_finiteType_properSmooth (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [Smooth f] :
    ∃ (R : Type u) (_ : CommRing R) (φ : R →+* A) (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R))
      (q' : X ⟶ Y), Algebra.FiniteType ℤ R ∧ Function.Injective φ ∧ IsProper h ∧ Smooth h ∧
        IsPullback q' f h (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨j, Y, h, q', hpr, hsm, hpb⟩ := exists_isPullback_affineStageCone_properSmooth f
  exact ⟨_, _, ((Scheme.ΓSpecIso (.of A)).hom.hom.comp
    (Algebra.adjoin ℤ ((j.unop : Finset Γ(Spec (.of A), ⊤)) :
      Set Γ(Spec (.of A), ⊤))).val.toRingHom),
    Y, h, q', finiteType_adjoinFinset_int _ j.unop,
    fun _ _ hxy => Subtype.ext ((Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective hxy),
    hpr, hsm, (affineStageCone_π_app_spec (.of A) j) ▸ hpb⟩

end AlgebraicGeometry.HodgeSpreadingOut
