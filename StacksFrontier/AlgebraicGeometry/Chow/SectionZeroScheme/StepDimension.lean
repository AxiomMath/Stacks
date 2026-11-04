module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Regular
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Hyperplane
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension

/-!
# The dimension estimates of the inductive step of Stacks 0FA9

Let `X` be locally of finite type over the base of chapter 42 and let `ℰ` be finite locally free
on `X`, with projective bundle `π : P = 𝐏(ℰ) ⟶ X` flat of relative dimension `d`. Let `s` be a
section of `ℰ` and `t` the image of `π^* s` in `𝒪_P(1)`. Then:

* `dim_δ(P) ≤ dim_δ(X) + d`, and `dim_δ(π⁻¹(Z)) ≤ dim_δ(Z) + d` for a closed subscheme `Z ⊆ X`;
* if `d = r + 1`, `dim_δ(X) ≤ n` and `dim_δ(Z(s)) ≤ n - r - 2`, every point `y` of `Z(t)` has
  `δ(y) ≤ n + r`, and if `δ(y) = n + r` the ideal of `Z(t)` at `y` contains a nonzerodivisor.

## Main results

* `Stacks.Chow.SectionZeroScheme.schemeDeltaDimension_bundle_le`: `dim_δ(P) ≤ n + d`.
* `Stacks.Chow.SectionZeroScheme.schemeDeltaDimension_comap_le`: `dim_δ(π⁻¹(Z)) ≤ k + d`.
* `Stacks.Chow.SectionZeroScheme.hyperplane_bundleSection_properties`: the two hypotheses of
  Stacks 02SQ for the hyperplane `Z(t)`, at a point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

/-- The `δ`-dimension of a closed subscheme depends only on its image. -/
theorem schemeDeltaDimension_congr_of_range_eq (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (i : Y ⟶ X) [IsClosedImmersion i]
    (j : Z ⟶ X) [IsClosedImmersion j] (h : Set.range i = Set.range j) :
    schemeDeltaDimension C (i ≫ p) = schemeDeltaDimension C (j ≫ p) :=
  Stacks.Chow.schemeDeltaDimension_eq_of_equal_ranges C p i j h

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
  (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
  [Flat (bundleProj F)] [LocallyOfFiniteType (bundleProj F)] (d : ℕ)
  (hd : AlgebraicGeometry.RelativeDimension (bundleProj F) d)

/-- Bound for a closed subscheme of `P` with the range of the pullback of a closed subscheme. -/
private theorem schemeDeltaDimension_bundle_le_of_range_eq
    (hd : AlgebraicGeometry.RelativeDimension (bundleProj F) d) {Z W : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : W ⟶ bundle F) [IsClosedImmersion g]
    (hrange : Set.range (pullback.fst (bundleProj F) i) = Set.range g) {k : ℤ}
    (hZ : schemeDeltaDimension C (i ≫ q) ≤ (k : EInt)) :
    schemeDeltaDimension C (g ≫ bundleProj F ≫ q) ≤ ((k + d : ℤ) : EInt) := by
  have h := schemeDeltaDimension_pullback_le C (bundleProj F ≫ q) q (bundleProj F) rfl d hd i k hZ
  rwa [schemeDeltaDimension_congr_of_range_eq C _ _ _ hrange] at h

include hd in
/-- **`dim_δ(P) ≤ n + d`.** -/
theorem schemeDeltaDimension_bundle_le {n : ℤ} (hX : schemeDeltaDimension C q ≤ (n : EInt)) :
    schemeDeltaDimension C (bundleProj F ≫ q) ≤ ((n + d : ℤ) : EInt) := by
  have hrange : Set.range (pullback.fst (bundleProj F) (𝟙 X)) =
      Set.range (𝟙 (bundle F) : bundle F ⟶ bundle F) := by
    rw [Set.range_eq_univ.2 (pullback.fst (bundleProj F) (𝟙 X)).surjective]
    exact (Set.range_eq_univ.2 (𝟙 (bundle F) : bundle F ⟶ bundle F).surjective).symm
  exact (schemeDeltaDimension_congr C (Category.id_comp (bundleProj F ≫ q))).symm.trans_le
    (schemeDeltaDimension_bundle_le_of_range_eq C q F d hd (𝟙 X) _ hrange
      ((schemeDeltaDimension_congr C (Category.id_comp q)).trans_le hX))

include hd in
/-- **`dim_δ(π⁻¹(Z(s))) ≤ dim_δ(Z(s)) + d`.** -/
theorem schemeDeltaDimension_comap_le (I : X.IdealSheafData) {k : ℤ}
    (hI : schemeDeltaDimension C (I.subschemeι ≫ q) ≤ (k : EInt)) :
    schemeDeltaDimension C ((I.comap (bundleProj F)).subschemeι ≫ bundleProj F ≫ q) ≤
      ((k + d : ℤ) : EInt) := by
  refine schemeDeltaDimension_bundle_le_of_range_eq C q F d hd _ _ ?_ hI
  rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
  rfl

omit [Flat (bundleProj F)] in
include hd in
/-- **The two hypotheses of [Stacks, Tag 02SQ] for the hyperplane `Z(t)`, at a point.** With
`d = r + 1`, `dim_δ(X) ≤ n` and `dim_δ(Z(s)) ≤ n - r - 2`: every point `y` of `Z(t)` has
`δ(y) ≤ n + r`, and if `δ(y) = n + r` the ideal of `Z(t)` at `y` contains a nonzerodivisor. -/
theorem hyperplane_bundleSection_properties [Flat (bundleProj F)] (r : ℕ) (hdr : d = r + 1)
    (s : Γ(F, ⊤)) {n : ℤ} (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C ((zeroSchemeOfSection X F s).subschemeι ≫ q) ≤
      ((n - (r + 2 : ℕ) : ℤ) : EInt)) (y : bundle F)
    (hyD : y ∈ (hyperplane (Stacks.ProjectiveBundleSplitting.tautologicalMap F (bundlePieces F))
      (pullbackGlobalSections (bundleProj F) F s)).support) :
    relativeDimension C.dimensionFunction (bundleProj F ≫ q) y ≤ n + r ∧
      (relativeDimension C.dimensionFunction (bundleProj F ≫ q) y = n + r →
      ∃ a ∈ nonZeroDivisors ((bundle F).presheaf.stalk y),
        a ∈ Stacks.AlgebraicGeometry.stalkIdeal (hyperplane
          (Stacks.ProjectiveBundleSplitting.tautologicalMap F (bundlePieces F))
          (pullbackGlobalSections (bundleProj F) F s)) y hyD) := by
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have hPdim := schemeDeltaDimension_bundle_le C q F d hd hX
  by_cases hx : bundleProj F y ∈ (zeroSchemeOfSection X F s).supportSet
  · have hy : y ∈ ((zeroSchemeOfSection X F s).comap (bundleProj F)).support := by
      rw [Scheme.IdealSheafData.support_comap]
      exact (Scheme.IdealSheafData.mem_supportSet_iff_mem_support).1 hx
    have hle := relativeDimension_le_of_schemeDeltaDimension_le C (bundleProj F ≫ q)
      ((zeroSchemeOfSection X F s).comap (bundleProj F)).subschemeι
      (schemeDeltaDimension_comap_le C q F d hd _ hZ) ⟨y, hy⟩
    change relativeDimension C.dimensionFunction (bundleProj F ≫ q) y ≤ _ at hle
    push_cast at hle
    exact ⟨by omega, fun _ => by omega⟩
  · obtain ⟨a, ha, hmem⟩ :=
      exists_nonZeroDivisor_mem_stalkIdeal_bundleSectionOf F (bundlePieces F) s y hyD hx
    have hmem' : a ∈ IdealSheafData.stalk (hyperplane
        (Stacks.ProjectiveBundleSplitting.tautologicalMap F (bundlePieces F))
        (pullbackGlobalSections (bundleProj F) F s)) y :=
      (stalkIdeal_eq_stalk _ y hyD) ▸ hmem
    have hm : a ∈ IsLocalRing.maximalIdeal ((bundle F).presheaf.stalk y) :=
      (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ y).2 hyD hmem'
    obtain ⟨η, hη, hne⟩ := exists_specializes_ne_of_mem_maximalIdeal a ha hm
    have hle := relativeDimension_le_sub_one_of_specializes C (bundleProj F ≫ q) hPdim hη hne
    exact ⟨by omega, fun _ => ⟨a, ha, hmem⟩⟩

end Stacks.Chow.SectionZeroScheme

end
