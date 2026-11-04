module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula

/-!
# The canonical Frobenius twist on a block fixed by `π̄`

Let `Y` be finite étale over a finite field `k` and `k̄` an algebraically closed extension of `k`.
The sections of `C|_{Y_k̄}` over `Y_k̄` are the product of the blocks indexed by the `k̄`-points
`ȳ` of `Y_k̄` (`Stacks.EtaleCohomology.blockInclusion`, `Stacks.EtaleCohomology.blockRestriction`),
and the canonical Frobenius twist sends the block at `ȳ ≫ π̄` to the block at `ȳ`. Since
`ȳ ↦ ȳ ≫ π̄` is injective, the block at a point fixed by `π̄` is stable under the twist, which
acts on it by the twist at that point: the inclusion of the block intertwines
`Stacks.EtaleCohomology.pointTwist` with `Stacks.EtaleCohomology.sectionsTwistEndo`.

## Main results

* `Stacks.EtaleCohomology.etaleSections_eq_of_comp_geometricFrobeniusBaseChange_eq`:
  `ȳ ↦ ȳ ≫ π̄` is injective on the `k̄`-points of `Y_k̄`.
* `Stacks.EtaleCohomology.blockInclusion_comp_sectionsTwistEndo_of_eq`: at a `π̄`-fixed point,
  `ι_ȳ ≫ T = T_ȳ ≫ ι_ȳ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

section Injective

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [CharP k p] in
/-- `Spec` of the arithmetic Frobenius of `k̄` is an epimorphism, being an isomorphism. -/
lemma epi_specMap_arithmeticFrobenius :
    Epi (Spec.map (CommRingCat.ofHom
      (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom)) := by
  have h : Spec.map (CommRingCat.ofHom
        (arithmeticFrobenius k kbar p q hcard).symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) =
        𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext z
    exact (arithmeticFrobenius k kbar p q hcard).symm_apply_apply z
  exact epi_of_epi_fac h

omit [Etale Y.hom] [IsFinite Y.hom] in
/-- **`ȳ ↦ ȳ ≫ π̄` is injective on the `k̄`-points of `Y_k̄`**: on the first factor it is
`ȳ ↦ Spec(σ) ≫ ȳ` for the arithmetic Frobenius `σ` of `k̄`, an isomorphism, and on the second
factor it is the identity. -/
lemma etaleSections_eq_of_comp_geometricFrobeniusBaseChange_eq
    {y y' : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))}
    (h : y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard =
      y'.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) : y = y' := by
  have := epi_specMap_arithmeticFrobenius kbar p q hcard
  refine Subtype.ext (pullback.hom_ext ?_ (y.2.trans y'.2.symm))
  have h₁ := congrArg (· ≫ pullback.fst Y.hom (specAlgebraMap k kbar)) h
  simp only [Category.assoc, geometricFrobeniusBaseChange_comp_fst] at h₁
  rw [← Category.assoc, ← Category.assoc, comp_geometricFrobenius_left,
    comp_geometricFrobenius_left] at h₁
  exact (cancel_epi _).1 h₁

end Injective

section Twist

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The inclusion of a `π̄`-fixed block intertwines the twist there with the canonical twist**:
`ι_ȳ ≫ T = T_ȳ ≫ ι_ȳ` for `ȳ = ȳ ≫ π̄`. Through the decomposition of the identity into blocks,
`ι_ȳ ≫ T ≫ r_{ȳ'} = ι_ȳ ≫ r_{ȳ' ≫ π̄} ≫ T_{ȳ'}` vanishes unless `ȳ' ≫ π̄ = ȳ = ȳ ≫ π̄`, that is
`ȳ' = ȳ`. -/
lemma blockInclusion_comp_sectionsTwistEndo_of_eq
    (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (hy : y.1 = y.1 ≫ geometricFrobeniusBaseChange Y kbar p q hcard) :
    blockInclusion Λ Y kbar y ≫ sectionsTwistEndo Λ Y kbar p q hcard =
      pointTwist Λ Y kbar p q hcard hy ≫ blockInclusion Λ Y kbar y := by
  classical
  calc blockInclusion Λ Y kbar y ≫ sectionsTwistEndo Λ Y kbar p q hcard
      = blockInclusion Λ Y kbar y ≫ sectionsTwistEndo Λ Y kbar p q hcard ≫
          ∑ y', blockRestriction Λ Y kbar y' ≫ blockInclusion Λ Y kbar y' := by
        rw [sum_blockRestriction_comp_blockInclusion Λ Y kbar, Category.comp_id]
    _ = ∑ y', blockInclusion Λ Y kbar y ≫ (sectionsTwistEndo Λ Y kbar p q hcard ≫
          blockRestriction Λ Y kbar y') ≫ blockInclusion Λ Y kbar y' := by
        simp only [Preadditive.comp_sum, Category.assoc]
    _ = blockInclusion Λ Y kbar y ≫ (sectionsTwistEndo Λ Y kbar p q hcard ≫
          blockRestriction Λ Y kbar y) ≫ blockInclusion Λ Y kbar y := by
        refine Finset.sum_eq_single y (fun y' _ hne => ?_) (fun h => absurd (Finset.mem_univ y) h)
        rw [sectionsTwistEndo_comp_blockRestriction Λ Y kbar p q hcard
            (y₂ := frobeniusSection Y kbar p q hcard y') rfl, Category.assoc,
          blockInclusion_comp_blockRestriction_of_ne_assoc, zero_comp]
        intro he
        exact hne (etaleSections_eq_of_comp_geometricFrobeniusBaseChange_eq Y kbar p q hcard
          ((congrArg Subtype.val he).symm.trans hy))
    _ = pointTwist Λ Y kbar p q hcard hy ≫ blockInclusion Λ Y kbar y := by
        rw [sectionsTwistEndo_comp_blockRestriction Λ Y kbar p q hcard hy, Category.assoc,
          blockInclusion_comp_blockRestriction_self_assoc]

end Twist

end Stacks.EtaleCohomology

end
