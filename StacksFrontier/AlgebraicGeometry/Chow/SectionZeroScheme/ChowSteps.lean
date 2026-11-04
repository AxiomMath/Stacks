module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.StepDimension
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.WhitneyTop
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper

/-!
# The cycle computations of the inductive step of Stacks 0FA9

The flat pullback of the fundamental class of `X` along a flat morphism `π : P ⟶ X` of relative
dimension `d` is the fundamental class of `P`, and the flat pullback of the class of a closed
subscheme `Z ⊆ X` is the class of `π⁻¹(Z)` ([Stacks, Tag 02RE]). For closed subschemes
`Z' ⊆ Y ⊆ P` with `Y ⊆ Z'' ⊆ P`, the inverse image of `Z''` in `Y`, pushed back into `P`, is `Z''`
again. And the kernel of an invertible quotient pulls back to the kernel of the pulled-back
quotient.

## Main results

* `Stacks.Chow.SectionZeroScheme.flatPullbackChow_mk_fundamental`.
* `Stacks.Chow.SectionZeroScheme.flatPullbackChow_mk_closedSubscheme`.
* `Stacks.Chow.SectionZeroScheme.ker_comap_subschemeι_comp`.
* `Stacks.Chow.SectionZeroScheme.kernelPullbackIso`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (d : ℕ)
  (hd : AlgebraicGeometry.RelativeDimension π d)

/-- **The flat pullback of the class of a closed subscheme is the class of its inverse image**
([Stacks, Tag 02RE]). -/
theorem flatPullbackChow_mk_closedSubscheme (I : X.IdealSheafData) (k : ℤ)
    (hI : schemeDeltaDimension C (I.subschemeι ≫ q) ≤ (k : EInt))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (π ≫ q) q π rfl d hd k) :
    flatPullbackChow C (π ≫ q) q π rfl d hd k hfac
        (QuotientAddGroup.mk' (rationalEquivalences C q k)
          (cycleAssociatedToClosedSubscheme C q I.subschemeι k)) =
      QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) (k + d))
        (cycleAssociatedToClosedSubscheme C (π ≫ q) (I.comap π).subschemeι (k + d)) := by
  rw [flatPullbackChow_mk, flatPullback_cycleAssociatedToClosedSubscheme_of_le C (π ≫ q) q π rfl
    d hd I.subschemeι k hI]
  congr 1
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C (π ≫ q) _ _ (I.comapIso π).symm
    (I.comapIso_inv_subschemeι π) _

/-- **The flat pullback of the fundamental class is the fundamental class**
([Stacks, Tag 02RE]). -/
theorem flatPullbackChow_mk_fundamental (k : ℤ)
    (hX : schemeDeltaDimension C q ≤ (k : EInt))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (π ≫ q) q π rfl d hd k) :
    flatPullbackChow C (π ≫ q) q π rfl d hd k hfac
        (QuotientAddGroup.mk' (rationalEquivalences C q k)
          (cycleAssociatedToClosedSubscheme C q (𝟙 X) k)) =
      QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) (k + d))
        (cycleAssociatedToClosedSubscheme C (π ≫ q) (𝟙 P) (k + d)) := by
  rw [flatPullbackChow_mk, flatPullback_cycleAssociatedToClosedSubscheme_of_le C (π ≫ q) q π rfl
    d hd (𝟙 X) k ((schemeDeltaDimension_congr C (Category.id_comp q)).trans_le hX)]
  congr 1
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C (π ≫ q) _ _
    (asIso (pullback.fst π (𝟙 X))) (Category.comp_id _) _

/-- **The inverse image of a closed subscheme containing `Y`, pushed back along `Y ⊆ P`.** If
`j : Y ⟶ P` is a closed immersion and `I ⊇ Y`, i.e. `ker j ≤ I`, then the closed subscheme
`j⁻¹(I) ⊆ Y` is `I` as a closed subscheme of `P`. -/
theorem ker_comap_subschemeι_comp {Y : Scheme.{u}} (j : Y ⟶ P) [IsClosedImmersion j]
    (I : P.IdealSheafData) (hI : j.ker ≤ I) :
    ((I.comap j).subschemeι ≫ j).ker = I := by
  apply le_antisymm
  · -- `I` factors through `j⁻¹(I) ⟶ Y ⟶ P`
    obtain ⟨a, ha⟩ := (_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker
      j.ker I.subschemeι).2 (by rwa [Scheme.IdealSheafData.ker_subschemeι])
    have h0 : (asIso j.toImage).inv ≫ j = j.ker.subschemeι := by
      rw [Iso.inv_comp_eq]
      exact j.toImage_imageι.symm
    have hb : (a ≫ (asIso j.toImage).inv) ≫ j = I.subschemeι := by
      rw [Category.assoc, h0, ha]
    have hpb := isPullback_comapSubschemeMap I j
    let c := hpb.lift (a ≫ (asIso j.toImage).inv) (𝟙 _) (by rw [hb, Category.id_comp])
    have hc : c ≫ (I.comap j).subschemeι ≫ j = I.subschemeι := by
      rw [← Category.assoc, hpb.lift_fst, hb]
    have hle := Scheme.Hom.le_ker_comp c ((I.comap j).subschemeι ≫ j)
    rwa [hc, Scheme.IdealSheafData.ker_subschemeι] at hle
  · exact (_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker I _).1
      ⟨comapSubschemeMap I j, comapSubschemeMap_comp_subschemeι I j⟩

/-- **The kernel of an invertible quotient pulls back to the kernel of the pulled-back
quotient.** -/
def kernelPullbackIso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {M L : Y.Modules} (q₀ : M ⟶ L) [Epi q₀]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    kernel ((Scheme.Modules.pullback g).map q₀) ≅ (Scheme.Modules.pullback g).obj (kernel q₀) :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _)
    (Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible g q₀
      inferInstance hL).fIsKernel

include hd in
/-- **`dim_δ(π⁻¹(Z)) ≤ dim_δ(Z) + d`** along a flat morphism of relative dimension `d`
([Stacks, Tag 02RE]). -/
theorem schemeDeltaDimension_comap_le_of_flat (I : X.IdealSheafData) {k : ℤ}
    (hI : schemeDeltaDimension C (I.subschemeι ≫ q) ≤ (k : EInt)) :
    schemeDeltaDimension C ((I.comap π).subschemeι ≫ π ≫ q) ≤ ((k + d : ℤ) : EInt) := by
  have h := schemeDeltaDimension_pullback_le C (π ≫ q) q π rfl d hd I.subschemeι k hI
  have hrange : Set.range (pullback.fst π I.subschemeι) = Set.range (I.comap π).subschemeι := by
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    rfl
  rwa [schemeDeltaDimension_congr_of_range_eq C _ _ _ hrange] at h

/-- The image of a closed immersion is the image of the closed immersion of its kernel. -/
theorem range_eq_range_ker_subschemeι {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j] :
    Set.range j = Set.range j.ker.subschemeι := by
  conv_lhs => rw [← j.toImage_imageι]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [Set.range_eq_univ.2 j.toImage.surjective, Set.image_univ]

include hd in
/-- **`dim_δ(P) ≤ dim_δ(X) + d`** along a flat morphism of relative dimension `d`. -/
theorem schemeDeltaDimension_le_of_flat {n : ℤ} (hX : schemeDeltaDimension C q ≤ (n : EInt)) :
    schemeDeltaDimension C (π ≫ q) ≤ ((n + d : ℤ) : EInt) := by
  have h := schemeDeltaDimension_pullback_le C (π ≫ q) q π rfl d hd
    (𝟙 X) n ((schemeDeltaDimension_congr C (Category.id_comp q)).trans_le hX)
  have hrange : Set.range (pullback.fst π (𝟙 X)) = Set.range (𝟙 P : P ⟶ P) := by
    rw [Set.range_eq_univ.2 (pullback.fst π (𝟙 X)).surjective,
      Set.range_eq_univ.2 (𝟙 P : P ⟶ P).surjective]
  rw [schemeDeltaDimension_congr_of_range_eq C _ _ _ hrange] at h
  exact (schemeDeltaDimension_congr C (Category.id_comp (π ≫ q))).symm.trans_le h

end Stacks.Chow.SectionZeroScheme

end
