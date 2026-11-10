module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOrigin
public import StacksCore.Tactic.StacksAttribute

/-!
# Global sections of affine space with the origin doubled, and its non-affineness

In positive dimension the coordinate morphism from affine space with its origin doubled to
affine space identifies the polynomial ring with the ring of global sections of the structure
sheaf. Since the coordinate morphism carries the two distinct origins to the same point, the
scheme is not affine.

## Main results

* `AlgebraicGeometry.isIso_coordinateMorphism_globalSections`: the canonical homomorphism from
  the polynomial ring to the global sections is an isomorphism.
* `AlgebraicGeometry.not_isAffine_affineSpaceWithDoubledZero`: affine space of positive
  dimension with its origin doubled is not an affine scheme.
* `AlgebraicGeometry.opensRange_glueData_f`: for two distinct charts, the overlap map has range
  the complement of the origin.
* `AlgebraicGeometry.glueData_t_comp_f`: the transition map composed with an overlap map is the
  other overlap map.
* `AlgebraicGeometry.comp_chartInclusion_eq`: a morphism into affine space avoiding the origin
  composes equally with the two chart inclusions.
* `AlgebraicGeometry.origin_notMem_range_other_chart`: the origin of one chart is not in the
  range of the other.

## References

* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The gluing maps of the doubled-origin datum are open immersions. -/
instance glueData_f_isOpenImmersion (k : Type u) [Field k] (n : ℕ)
    (i j : ULift.{u} (Fin 2)) :
    IsOpenImmersion ((doubledZeroGlueData k n).toGlueData.f i j) :=
  (doubledZeroGlueData k n).f_open i j

/-- For two distinct charts, the overlap maps onto the complement of the origin. -/
lemma opensRange_glueData_f (k : Type u) [Field k] (n : ℕ)
    {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    ((doubledZeroGlueData k n).toGlueData.f i j).opensRange = puncturedAffineSpace k n := by
  dsimp [doubledZeroGlueData, doubledZeroPreGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f']
  split_ifs with h
  · exact absurd h hij
  · rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- For two distinct charts, the transition map composed with the overlap map of the second chart
is the overlap map of the first. -/
lemma glueData_t_comp_f (k : Type u) [Field k] (n : ℕ)
    {i j : ULift.{u} (Fin 2)} (hij : i ≠ j) :
    (doubledZeroGlueData k n).toGlueData.t i j ≫ (doubledZeroGlueData k n).toGlueData.f j i =
      (doubledZeroGlueData k n).toGlueData.f i j := by
  simp [doubledZeroGlueData, doubledZeroPreGlueData,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', hij, hij.symm]

/-- The origin of affine space is not in the complement of the origin. -/
lemma affineOrigin_notMem_puncturedAffineSpace (k : Type u) [Field k] (n : ℕ) :
    affineOrigin k n ∉ puncturedAffineSpace k n := by
  intro hmem
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hi (by simp [affineOrigin, RingHom.mem_ker])

/-- The origin of one chart is not in the range of the other chart. -/
lemma origin_notMem_range_other_chart (k : Type u) [Field k] (n : ℕ) (i j : Fin 2)
    (hij : i ≠ j) :
    chartInclusion k n i (affineOrigin k n) ∉ Set.range (chartInclusion k n j) := by
  have hne : (ULift.up i : ULift.{u} (Fin 2)) ≠ ULift.up j := fun h => hij (congrArg ULift.down h)
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, -⟩ :=
    ((doubledZeroGlueData k n).ι_eq_iff (ULift.up i) (ULift.up j) _ _).mp hx.symm
  refine affineOrigin_notMem_puncturedAffineSpace k n ?_
  rw [← opensRange_glueData_f k n hne]
  exact ⟨y, hy⟩

/-- A morphism into affine space whose image avoids the origin composes equally with the two
chart inclusions. -/
lemma comp_chartInclusion_eq (k : Type u) [Field k] (n : ℕ) {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of (MvPolynomial (Fin n) k)))
    (hg : Set.range g.base ⊆ (puncturedAffineSpace k n : Set _)) :
    g ≫ chartInclusion k n 0 = g ≫ chartInclusion k n 1 := by
  have hij : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by decide
  have hrange : Set.range g.base ⊆
      Set.range ((doubledZeroGlueData k n).toGlueData.f (ULift.up 0) (ULift.up 1)).base := by
    refine hg.trans fun z hz => ?_
    rw [← opensRange_glueData_f k n hij] at hz
    exact hz
  obtain ⟨v, rfl⟩ : ∃ v, v ≫ (doubledZeroGlueData k n).toGlueData.f (ULift.up 0) (ULift.up 1) = g :=
    ⟨_, IsOpenImmersion.lift_fac
      ((doubledZeroGlueData k n).toGlueData.f (ULift.up 0) (ULift.up 1)) g hrange⟩
  have h := (doubledZeroGlueData k n).glue_condition (ULift.up 0) (ULift.up 1)
  rw [← Category.assoc, glueData_t_comp_f k n hij] at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (v ≫ ·) h.symm).trans (Category.assoc _ _ _).symm)

section Helpers

private lemma chart_sections_eq (k : Type u) [Field k] (n : ℕ) (hn : 0 < n)
    (s : Γ(affineSpaceWithDoubledZero k n, ⊤)) :
    (chartInclusion k n 0).appTop s = (chartInclusion k n 1).appTop s := by
  classical
  let x : MvPolynomial (Fin n) k := MvPolynomial.X ⟨0, hn⟩
  let R := CommRingCat.of (MvPolynomial (Fin n) k)
  let S := CommRingCat.of (Localization.Away x)
  let b : Spec S ⟶ Spec (.of (MvPolynomial (Fin n) k)) :=
    Spec.map (CommRingCat.ofHom (algebraMap _ _))
  have hbRange : b.opensRange = PrimeSpectrum.basicOpen x := by
    simpa only [b] using (Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of (MvPolynomial (Fin n) k)) x)
  have hg : Set.range b.base ⊆ (puncturedAffineSpace k n : Set _) := by
    rw [← Scheme.Hom.coe_opensRange, hbRange]
    exact (le_iSup_of_le ⟨0, hn⟩ le_rfl : PrimeSpectrum.basicOpen x ≤ puncturedAffineSpace k n)
  have hb_inj : Function.Injective b.appTop.hom := by
    refine Function.Injective.of_comp (f := (Scheme.ΓSpecIso S).hom.hom) ?_
    rw [← RingHom.coe_comp, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
      CommRingCat.hom_comp, RingHom.coe_comp]
    exact (IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (show x ≠ 0 from MvPolynomial.X_ne_zero _))).comp
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
  apply hb_inj
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using
    congrArg (fun z : Spec S ⟶ affineSpaceWithDoubledZero k n => z.appTop s)
      (comp_chartInclusion_eq k n b hg)

private lemma chartOrigins_ne (k : Type u) [Field k] (n : ℕ) :
    chartInclusion k n 0 (affineOrigin k n) ≠ chartInclusion k n 1 (affineOrigin k n) :=
  fun heq => origin_notMem_range_other_chart k n 0 1 (by decide) ⟨affineOrigin k n, heq.symm⟩

end Helpers

/-- In positive dimension, every global function on affine space with doubled origin is induced
uniquely by a polynomial via the coordinate morphism. -/
@[stacks 01JD "global_sections", ega "I 5.5.11" "more general", sga "6 II 2.2.7.2" "more general"]
theorem isIso_coordinateMorphism_globalSections (k : Type u) [Field k]
    (n : ℕ) (hn : 0 < n) :
    IsIso ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv ≫
      (coordinateMorphism k n).appTop) := by
  classical
  let R := CommRingCat.of (MvPolynomial (Fin n) k)
  let q : R ⟶ Γ(affineSpaceWithDoubledZero k n, ⊤) :=
    (Scheme.ΓSpecIso R).inv ≫ (coordinateMorphism k n).appTop
  have hchart (i : Fin 2) (a : MvPolynomial (Fin n) k) :
      (chartInclusion k n i).appTop.hom (q.hom a) = (Scheme.ΓSpecIso R).inv.hom a := by
    have hc : chartInclusion k n i ≫ coordinateMorphism k n = 𝟙 _ :=
      (coordinateMorphismData k n).property i
    have h : (coordinateMorphism k n).appTop ≫ (chartInclusion k n i).appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hc, Scheme.Hom.id_appTop]
    simpa [q] using congrArg (fun g => g.hom ((Scheme.ΓSpecIso R).inv.hom a)) h
  refine (ConcreteCategory.isIso_iff_bijective q).2 ⟨fun a a' haa' => ?_, fun s => ?_⟩
  · have h := congrArg (chartInclusion k n 0).appTop.hom haa'
    rw [hchart 0 a, hchart 0 a'] at h
    exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective h
  · let p := (Scheme.ΓSpecIso R).hom.hom ((chartInclusion k n 0).appTop.hom s)
    have hcan : (Scheme.ΓSpecIso R).inv.hom p = (chartInclusion k n 0).appTop.hom s := by
      simp [p]
    refine ⟨p, (doubledZeroGlueData k n).openCover.ext_elem (q.hom p) s fun ⟨i⟩ => ?_⟩
    change (chartInclusion k n i).appTop.hom (q.hom p) = (chartInclusion k n i).appTop.hom s
    fin_cases i
    · simpa using (hchart 0 p).trans hcan
    · simpa using (hchart 1 p).trans (hcan.trans (chart_sections_eq k n hn s))

/-- Affine space of positive dimension with its origin doubled is not affine. -/
@[stacks 01JD "not_affine"]
theorem not_isAffine_affineSpaceWithDoubledZero (k : Type u) [Field k]
    (n : ℕ) (hn : 0 < n) :
    ¬ IsAffine (affineSpaceWithDoubledZero k n) := by
  intro hX
  let f := coordinateMorphism k n
  have : IsIso ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv ≫ f.appTop) :=
    isIso_coordinateMorphism_globalSections k n hn
  let g := AffineScheme.ofHom f
  have : IsIso g := (isIso_op_iff g).mp
    ((isIso_iff_of_reflects_iso g.op AffineScheme.Γ).mp
      (show IsIso (AffineScheme.Γ.map g.op) from
        IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv f.appTop))
  have : IsIso f := Functor.map_isIso AffineScheme.forgetToScheme g
  exact chartOrigins_ne k n ((show Function.Injective f from by
    intro x y hxy
    have := congrArg (inv f) hxy
    change (f ≫ inv f) x = (f ≫ inv f) y at this
    simpa using this) (by rw [coordinateMorphism_map_origin, coordinateMorphism_map_origin]))

end AlgebraicGeometry

end
