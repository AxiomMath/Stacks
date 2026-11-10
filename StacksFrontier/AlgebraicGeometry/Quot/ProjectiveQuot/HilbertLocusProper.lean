module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Representability
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Proper
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The Hilbert locus `Z_P` is proper

Let `p ≤ N`. The monomorphism `Z_P ⟶ G = G(N - p, N)` representing `Quot^P`
(`AlgebraicGeometry.ProjectiveQuot.hilbertFunctorIso`) is proper: it is quasi-compact and locally
of finite type (an open and closed immersion followed by the flat locus, a monomorphism of finite
presentation), separated (a monomorphism), and satisfies the existence part of the valuative
criterion: a point of `Quot^P` over the fraction field `K` of a valuation ring `R` extends to a
point over `R` (`AlgebraicGeometry.ProjectiveQuot.exists_baseChange_eq_of_valuationRing`, the flat
closure), whose classifying morphism agrees with the given `Spec R ⟶ G` because `G` is separated
(uniqueness half of the valuative criterion for `G ⟶ Spec ℤ`). As `G` is proper over `Spec ℤ`
(`AlgebraicGeometry.Grassmannian.isProper_terminalFrom`), so is `Z_P`. This is the properness step
of the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isProper_hilbertLocusHom`: the morphism `Z_P ⟶ G` is proper.
* `AlgebraicGeometry.ProjectiveQuot.isProper_hilbertLocus_terminalFrom`: `Z_P` is proper over
  `Spec ℤ`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0BX5](https://stacks.math.columbia.edu/tag/0BX5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ} {P : Polynomial ℚ}

/-- The inclusion of `Z_P` in the flat locus is quasi-compact: it is an open immersion with closed
image, hence a closed embedding. -/
instance quasiCompact_hilbertLocus_ι :
    QuasiCompact (hilbertLocus.{u} n r P).ι := by
  have hcl : Topology.IsClosedEmbedding (hilbertLocus.{u} n r P).ι :=
    ⟨(hilbertLocus.{u} n r P).ι.isOpenEmbedding.isEmbedding, by
      rw [Scheme.Opens.range_ι]
      exact (isClopen_hilbertLocusSet.{u} n r P).isClosed⟩
  exact ⟨fun _ _ hU => hcl.isCompact_preimage hU⟩

/-- The morphism `Z_P ⟶ G` is quasi-compact. -/
instance quasiCompact_hilbertLocusHom : QuasiCompact (hilbertLocusHom.{u} n r P) := by
  have := (finitePresentation_flatLocus_hom.{u} n r P).2.1
  unfold hilbertLocusHom
  infer_instance

/-- The morphism `Z_P ⟶ G` is locally of finite type. -/
instance locallyOfFiniteType_hilbertLocusHom :
    LocallyOfFiniteType (hilbertLocusHom.{u} n r P) := by
  have : LocallyOfFinitePresentation (flatLocus.{u} n r P).hom :=
    (finitePresentation_flatLocus_hom.{u} n r P).1
  unfold hilbertLocusHom
  infer_instance

/-- **Valuative existence for `Z_P ⟶ G`.** -/
theorem valuativeCriterionExistence_hilbertLocusHom
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P)) :
    ValuativeCriterion.Existence (hilbertLocusHom.{u} n r P) := by
  intro S
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))
  let e := hilbertLocusEquiv hp
  set K₀ := (e (Spec (.of S.K))).symm S.i₁
  obtain ⟨K₁, hK₁, hbc⟩ :=
    exists_baseChange_eq_of_valuationRing (n := n) (r := r) P S.R S.K K₀.1 K₀.2
  have hK₀ : toGrassmannian hp K₀.2 = S.i₁ ≫ hilbertLocusHom.{u} n r P := by
    rw [← toHilbertLocus_comp]
    exact congrArg (· ≫ hilbertLocusHom.{u} n r P) ((e (Spec (.of S.K))).apply_symm_apply S.i₁)
  have hι : ι ≫ toGrassmannian hp hK₁ = toGrassmannian hp K₀.2 := by
    rw [comp_toGrassmannian]
    congr 1
  have hbot : toGrassmannian hp hK₁ = S.i₂ := by
    let s := terminal.from (quotGrassmannian.{u} n r P)
    let S' : ValuativeCommSq s :=
      { R := S.R, K := S.K, i₁ := S.i₁ ≫ hilbertLocusHom.{u} n r P,
        i₂ := S.i₂ ≫ s, commSq := ⟨by rw [← Category.assoc, S.commSq.w, Category.assoc]⟩ }
    have := IsSeparated.valuativeCriterion s S'
    let l₁ : S'.commSq.LiftStruct :=
      { l := toGrassmannian hp hK₁, fac_left := hι.trans hK₀,
        fac_right := terminal.hom_ext _ _ }
    let l₂ : S'.commSq.LiftStruct :=
      { l := S.i₂, fac_left := S.commSq.w.symm, fac_right := rfl }
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  refine ⟨⟨{ l := toHilbertLocus hp hK₁, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (hilbertLocusHom.{u} n r P)).1
    rwa [Category.assoc, toHilbertLocus_comp, ← hK₀]
  · rw [toHilbertLocus_comp, hbot]

/-- **`Z_P ⟶ G` is proper.** -/
theorem isProper_hilbertLocusHom
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P)) :
    IsProper (hilbertLocusHom.{u} n r P) :=
  IsProper.of_valuativeCriterion _ (ValuativeCriterion.iff.2
    ⟨valuativeCriterionExistence_hilbertLocusHom hp, IsSeparated.valuativeCriterion _⟩)

/-- **`Z_P` is proper over `Spec ℤ`.** -/
theorem isProper_hilbertLocus_terminalFrom
    (hp : quotRank.{u} n r P ≤ freeRank.{u} n r (regularityIndex.{u} n r P)) :
    IsProper (terminal.from (hilbertLocus.{u} n r P).toScheme) := by
  have := isProper_hilbertLocusHom hp
  rw [← terminal.comp_from (hilbertLocusHom.{u} n r P)]
  infer_instance

end AlgebraicGeometry.ProjectiveQuot

end
