module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.RingTheory.Koszul.TorComparison.Resolution

/-!
# The Koszul complex as a K-flat model of the quotient in the derived category

Let `R` be a commutative ring and `f₁, …, f_r ∈ R`. Re-indexing the Koszul complex
`K_•(f₁, …, f_r)` along `j ↦ -j` turns it into a cochain complex concentrated in degrees `≤ 0`
whose terms are finite free `R`-modules; being bounded above with flat terms it is K-flat
([Stacks, Tag 064K]). When the sequence is Koszul-regular the augmentation onto
`R ⧸ (f₁, …, f_r)` is a quasi-isomorphism, so this cochain complex represents the quotient in the
derived category.

## Main definitions

* `Koszul.seqCochainComplex` — the Koszul complex of a sequence, re-indexed as a cochain complex
  over `ℤ` in degrees `≤ 0`.

## Main results

* `Koszul.kFlat_seqCochainComplex` — it is K-flat.
* `Koszul.nonempty_Q_obj_seqCochainComplex_iso_single` — for a Koszul-regular sequence its image
  in the derived category is `R ⧸ (f₁, …, f_r)` placed in degree zero.

## Implementation notes

The re-indexing is `HomologicalComplex.extend` along `ComplexShape.embeddingDownNat`, the embedding
`ℕ → ℤ`, `j ↦ -j`, of the homological shape into the cohomological one.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 0623](https://stacks.math.columbia.edu/tag/0623)
* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The Koszul complex of `f₁, …, f_r` as a cochain complex.** Exterior degree `j` sits in
cohomological degree `-j`, so the complex is concentrated in degrees `≤ 0`. -/
abbrev seqCochainComplex (f : Fin r → R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat

/-- **The cochain Koszul complex is K-flat.** -/
theorem kFlat_seqCochainComplex (f : Fin r → R) : (seqCochainComplex f).KFlat :=
  CochainComplex.KFlat.kFlat_of_flat (seqCochainComplex f) 0

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **For a Koszul-regular sequence the cochain Koszul complex represents the quotient.** Its
image in the derived category of `R`-modules is `R ⧸ (f₁, …, f_r)` placed in degree zero. -/
theorem nonempty_Q_obj_seqCochainComplex_iso_single (f : Fin r → R)
    (hf : Koszul.IsKoszulRegular f) :
    Nonempty (DerivedCategory.Q.obj (seqCochainComplex f) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))) := by
  have hq : QuasiIso (koszulAugmentation f) := koszulAugmentation_quasiIso f hf
  have hq' : QuasiIso (HomologicalComplex.extendMap (koszulAugmentation f)
    ComplexShape.embeddingDownNat) := inferInstance
  refine ⟨asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap (koszulAugmentation f)
    ComplexShape.embeddingDownNat)) ≪≫ DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) 0 0 (by simp)) ≪≫ ?_⟩
  exact ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
    (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))).symm

end Derived

end Koszul

end
