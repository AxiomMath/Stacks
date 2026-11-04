module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.ProperSmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper smooth schemes over a ring come from finitely generated subrings

Let `f : X ⟶ Spec R` be proper and smooth of relative dimension `n`. Writing `R` as the filtered
colimit of its finitely generated `ℤ`-subalgebras `ℤ[s]`, `s ⊆ R` finite, the morphism `f` is
the base change of a proper morphism `Y ⟶ Spec ℤ[s]` smooth of relative dimension `n`, for
some finite `s` ([Stacks, Tags 01ZM, 081F, 0C0C, 0EY2]). This is the spreading out with which the
proof of [Stacks, Tag 0FW6] in characteristic zero reduces to positive characteristic.

## Main results

* `AlgebraicGeometry.exists_isPullback_specAdjoin_smoothOfRelativeDimension`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 0EY2](https://stacks.math.columbia.edu/tag/0EY2)
* [Stacks Project, Tag 0FW6](https://stacks.math.columbia.edu/tag/0FW6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism `X ≅ (Over.pullback p).obj Y` of objects over `S` exhibits `X.hom` as the base
change of `Y.hom` along `p`. -/
theorem isPullback_of_iso_overPullbackObj {C : Type*} [Category C] [HasPullbacks C] {S T : C}
    {p : S ⟶ T} {X : Over S} {Y : Over T} (e : X ≅ (Over.pullback p).obj Y) :
    IsPullback (e.hom.left ≫ pullback.fst Y.hom p) X.hom Y.hom p := by
  have he : e.hom.left ≫ pullback.snd Y.hom p = X.hom := Over.w e.hom
  refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e) rfl he
  show (e.hom.left ≫ pullback.fst Y.hom p) ≫ Y.hom = X.hom ≫ p
  rw [Category.assoc, pullback.condition, ← Category.assoc, he]

/-- A pullback square along `p` stays a pullback square along a factor `p'` of `p = p' ≫ m`, with
the base change of its right side along `m` as the new right side. -/
theorem isPullback_pullbackLift_of_comp {C : Type*} [Category C] {X Y Z W W' : C}
    {g₀ : X ⟶ Y} {f : X ⟶ W} {f₁ : Y ⟶ Z} {p : W ⟶ Z} {p' : W ⟶ W'} {m : W' ⟶ Z}
    [HasPullback f₁ m] (h : IsPullback g₀ f f₁ p) (hw : p' ≫ m = p) :
    IsPullback (pullback.lift g₀ (f ≫ p') (by rw [h.w, Category.assoc, hw])) f
      (pullback.snd f₁ m) p' := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f₁ m)
  rw [pullback.lift_fst, hw]
  exact h

/-- Smoothness and being syntomic of relative dimension `n` respect isomorphisms, and the latter is
stable under base change. -/
private theorem respectsIso_smooth_and_syntomicOfRelativeDimension (n : ℕ) :
    MorphismProperty.RespectsIso (@Smooth.{u}) ∧
      MorphismProperty.IsStableUnderBaseChange
        (@SyntomicOfRelativeDimension n : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.RespectsIso
        (@SyntomicOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
  have := syntomicOfRelativeDimension_isStableUnderBaseChange.{u} n
  ⟨MorphismProperty.IsStableUnderBaseChange.respectsIso, this,
    MorphismProperty.IsStableUnderBaseChange.respectsIso⟩

/-- If the base change of a morphism `f₁` of finite presentation to the limit of a cofiltered
system of qcqs schemes with affine transition maps is smooth and syntomic of relative dimension
`n`, then so is its base change to some stage. -/
theorem exists_smooth_syntomicOfRelativeDimension_pullbackSnd_of_isLimit_of_limitPullbackSnd
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (n : ℕ) {j : I}
    [CompactSpace (D.obj j)] [QuasiSeparatedSpace (D.obj j)] {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (f₁ : Y ⟶ D.obj j) [LocallyOfFinitePresentation f₁]
    (hsm : Smooth (pullback.snd f₁ (c.π.app j)))
    (hsyn : SyntomicOfRelativeDimension n (pullback.snd f₁ (c.π.app j))) :
    ∃ (k : I) (g : k ⟶ j), Smooth (pullback.snd f₁ (D.map g)) ∧
      SyntomicOfRelativeDimension n (pullback.snd f₁ (D.map g)) := by
  obtain ⟨_, _, _⟩ := respectsIso_smooth_and_syntomicOfRelativeDimension.{u} n
  let X₀ : Over (D.obj j) := Over.mk f₁
  let Y₀ : Over (D.obj j) := Over.mk (𝟙 (D.obj j))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  have : Smooth ((Over.pullback (c.π.app j)).map a).left :=
    (overPullback_map_homMk_toUnit_iff (@Smooth) f₁ (c.π.app j)).2 hsm
  obtain ⟨k₁, g₁, hk₁⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c j X₀ Y₀ a hc
  obtain ⟨k₂, g₂, hk₂⟩ := exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange n D c j
    X₀ Y₀ a hc ((overPullback_map_homMk_toUnit_iff (@SyntomicOfRelativeDimension n) f₁ _).2 hsyn)
  obtain ⟨k, b₁, b₂, hb⟩ := IsCofiltered.cospan g₁ g₂
  refine ⟨k, b₁ ≫ g₁, (overPullback_map_homMk_toUnit_iff (@Smooth) f₁ _).1 ?_,
    (overPullback_map_homMk_toUnit_iff (@SyntomicOfRelativeDimension n) f₁ _).1 ?_⟩
  · rw [D.map_comp]
    exact overPullback_map_comp (@Smooth) (D.map g₁) (D.map b₁) a hk₁
  · rw [hb, D.map_comp]
    exact overPullback_map_comp (@SyntomicOfRelativeDimension n) (D.map g₂) (D.map b₂) a hk₂

/-- **A proper morphism to `Spec R`, smooth of relative dimension `n`, is the base change of one to
the spectrum of a finitely generated `ℤ`-subalgebra of `R`.** The system of the spectra of the
finitely generated subalgebras has `Spec R` as its limit; the morphism, of finite presentation,
descends to a proper one over a stage ([Stacks, Tags 01ZM, 081F]), and smoothness and the
dimension of the fibres descend to a later stage ([Stacks, Tags 0C0C, 0EY2]). -/
@[ega "IV 17.7.9" "special case"]
theorem exists_isPullback_specAdjoin_smoothOfRelativeDimension (R : Type u) [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (j : (Finset R)ᵒᵖ) (Y : Scheme.{u}) (h : Y ⟶ (specAdjoinFinsetDiagram R).obj j)
      (q' : X ⟶ Y), IsProper h ∧ SmoothOfRelativeDimension n h ∧
        IsPullback q' f h ((specAdjoinFinsetCone R).π.app j) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  let D := specAdjoinFinsetDiagram R
  let c : Cone D := Cone.mk (Spec (.of R)) (specAdjoinFinsetCone R).π
  have hc : IsLimit c := isLimit_specAdjoinFinsetCone R
  have hnoeth : ∀ i, IsNoetherian (D.obj i) := fun i ↦ isNoetherian_specAdjoinFinsetDiagram_obj R i
  have : ∀ i, CompactSpace (D.obj i) := fun i => by have := hnoeth i; infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i => by have := hnoeth i; infer_instance
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  obtain ⟨j, Xj, hfpj, hprj, ⟨e⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D c hc (Over.mk f) hfp
  let f₁ : Xj.left ⟶ D.obj j := Xj.hom
  have : LocallyOfFinitePresentation f₁ := hfpj.1
  have : QuasiCompact f₁ := hfpj.2.1
  have : QuasiSeparated f₁ := hfpj.2.2
  have : IsProper f₁ := hprj
  have : CompactSpace Xj.left := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace Xj.left := quasiSeparatedSpace_of_quasiSeparated f₁
  have hsq₀ : IsPullback (e.hom.left ≫ pullback.fst f₁ (c.π.app j)) f f₁ (c.π.app j) :=
    isPullback_of_iso_overPullbackObj e
  obtain ⟨_, _, _⟩ := respectsIso_smooth_and_syntomicOfRelativeDimension.{u} n
  have hlim : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso], P f →
      P (pullback.snd f₁ (c.π.app j)) := fun P _ hP => by
    rw [← MorphismProperty.cancel_left_of_respectsIso P hsq₀.isoPullback.hom,
      hsq₀.isoPullback_hom_snd]
    exact hP
  obtain ⟨k, g, hsm, hsyn⟩ :=
    exists_smooth_syntomicOfRelativeDimension_pullbackSnd_of_isLimit_of_limitPullbackSnd D c hc n f₁
      (hlim _ inferInstance) (hlim _ ⟨syntomic_of_smooth f,
        fun x ↦ fiberDimensionAt_eq_of_smoothOfRelativeDimension f n x⟩)
  exact ⟨k, pullback f₁ (D.map g), pullback.snd f₁ (D.map g), _,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f₁ (D.map g)) inferInstance,
    Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ n hsyn.2,
    isPullback_pullbackLift_of_comp hsq₀ (c.w g)⟩

end AlgebraicGeometry
