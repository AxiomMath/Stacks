module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorizationForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionCurvatureCoordinates
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeTaylorFormulaCompleted
public import StacksFrontier.AlgebraicGeometry.Crystalline.RetractPairEquivalence

/-!
# The pairs over the completed envelopes of [Stacks, Lemma 60.17.5, Tag 07L5]

This module feeds the completed divided power envelopes of the source into the abstract
equivalence `Crystalline.retractPairEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/RetractPairEquivalence.lean`.

* `Crystalline.envelopeCoordinateData` — the coordinates of the `p`-adically completed envelope
  `D` of a polynomial presentation `A[x_i] → C`: its completed forms `Ω^*_D`, whose degree-one
  member is the `Ω_D` of [Stacks, Tag 07J9], with the universal differential, the basis
  `Crystalline.envelopeCompletionFormsBasis` of `Ω_D` on the `d x_i`, the composite coordinate
  derivations `∂_K` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeTaylorFormulaCompleted.lean`,
  and the reading of the curvature in the coordinates,
  `Crystalline.isCurvatureZero_envelopeCompletion_iff_coordOp_comm`.
* `Crystalline.envelopeRetractData` — the data of a retract `a : D → D'`, `b : D' → D`,
  `a ∘ b = id`, of divided power `A`-algebras compatible with the augmentations, `D'` any
  `p`-adically completed divided power ring; the comparisons of forms are the comparisons of
  completed forms `Crystalline.completedMapDifferentialForms` along `a` and `b`, in every degree,
  and Taylor's formula is `Crystalline.envelopeCompletion_taylor_levels`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open DividedPowers

universe u

namespace Crystalline

/-! ### The comparison of completed forms only depends on the algebra map -/

section Congr

variable (p : ℕ) (A : Type u) [CommRing A] {B C : Type u} [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {J : Ideal B} {K : Ideal C}
  (delta : DividedPowers J) (epsilon : DividedPowers K)

/-- The comparison of completed forms only depends on the algebra map. -/
theorem completedMapDifferentialForms_congr {f g : B →ₐ[A] C} (h : f = g)
    (hf : IsDPMorphism delta epsilon f.toRingHom) (hg : IsDPMorphism delta epsilon g.toRingHom)
    (i : ℕ) (x : completedDividedPowerForms p A delta i) :
    completedMapDifferentialForms p A delta epsilon f hf i x =
      completedMapDifferentialForms p A delta epsilon g hg i x := by
  subst h; rfl

end Congr

/-! ### The coordinates of the completed envelope of a polynomial presentation -/

section Coordinates

variable {A : DividedPowerRing.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  [Fact p.Prime] (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **The coordinates of the completed envelope `D`**: its completed forms `Ω^*_D` with the
universal differential, the basis `d x_i` of `Ω_D = Ω^1_D`, the composite coordinate derivations
`∂_K = ∏_i ∂_i^{k_i}`, and the reading of the curvature in the coordinates. -/
def envelopeCoordinateData : CompletedCoordinateData p (envelopeCompletion E p hp) where
  Om := envelopeCompletionForms E p hp
  wedge := envelopeCompletionFormsWedge E p hp
  deRham := completedDividedPowerDeRham p (A : Type u) (envelopeCompletion E p hp).dividedPowers
  diff := envelopeCompletionFormsDifferential E p hp
  diff_add := completedDividedPowerDifferentialOnRing_add p (A : Type u) _
  diff_mul := completedDividedPowerDifferentialOnRing_mul p (A : Type u) _
  diff_dpow _ hn _ hx := envelopeCompletionFormsDifferential_dpow E p hp hn hx
  isGradedLeibniz := isGradedLeibniz_envelopeCompletionForms E p hp
  wedge_anti := completedDividedPowerWedgeOnRing_one_add_swap p (A : Type u) _
  deRham_diff := completedDividedPowerDeRham_one_differentialOnRing p (A : Type u) _
  ι := ι
  coord := envelopeCompletionCoord E p hp
  basis := envelopeCompletionFormsBasis E p hp
  basis_eq := envelopeCompletionFormsBasis_apply E p hp
  deltaPow := envelopeCompletionDeltaPow E p hp (envelopeCompletionFormsBasis E p hp)
    (envelopeCompletionFormsBasis_apply E p hp)
  isThetaMonomialFamily := isThetaMonomialFamily_envelopeCompletionDeltaPow E p hp
    (envelopeCompletionFormsBasis E p hp) (envelopeCompletionFormsBasis_apply E p hp)
  isCurvatureZero_iff := fun hM nabla ↦
    isCurvatureZero_envelopeCompletion_iff_coordOp_comm E p hp hM nabla

end Coordinates

/-! ### The retract data -/

section Retract

variable {A : DividedPowerRing.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  [Fact p.Prime] (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))
  (D' : DividedPowerRing.{u}) [Algebra (A : Type u) (D' : Type u)]
  (a : DPMorphism (envelopeCompletion E p hp).dividedPowers D'.dividedPowers)
  (b : DPMorphism D'.dividedPowers (envelopeCompletion E p hp).dividedPowers)
  (ha : ∀ c : (A : Type u), a (algebraMap (A : Type u) (envelopeCompletion E p hp) c) =
    algebraMap (A : Type u) (D' : Type u) c)
  (hb : ∀ c : (A : Type u), b (algebraMap (A : Type u) (D' : Type u) c) =
    algebraMap (A : Type u) (envelopeCompletion E p hp) c)
  (hab : ∀ x : (D' : Type u), a (b x) = x)
  (hρ : ∀ y : envelopeCompletion E p hp, b (a y) - y ∈ (envelopeCompletion E p hp).ideal)

/-- **The retract data** of a retract `a ∘ b = id_{D'}` of divided power `A`-algebras, with the
completed envelope `D` of a polynomial presentation and an arbitrary divided power ring `D'`:
the comparisons of completed one-forms along `a` and `b`, and Taylor's formula for `ρ = b ∘ a`. -/
def envelopeRetractData :
    RetractData p (envelopeCompletion E p hp) (envelopeCoordinateData E p hp) :=
  let : Algebra (envelopeCompletion E p hp : Type u) (D' : Type u) := a.toRingHom.toAlgebra
  let : Algebra (D' : Type u) (envelopeCompletion E p hp : Type u) := b.toRingHom.toAlgebra
  have : IsScalarTower (D' : Type u) (envelopeCompletion E p hp : Type u) (D' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hab x).symm
  { ring := (D' : Type u)
    Om := completedDividedPowerForms p (A : Type u) D'.dividedPowers
    wedge := completedDividedPowerWedgeOnRing p (A : Type u) D'.dividedPowers
    deRham := completedDividedPowerDeRham p (A : Type u) D'.dividedPowers
    diff := completedDividedPowerDifferentialOnRing p (A : Type u) D'.dividedPowers
    diff_add := completedDividedPowerDifferentialOnRing_add p (A : Type u) _
    diff_mul := completedDividedPowerDifferentialOnRing_mul p (A : Type u) _
    isGradedLeibniz := isGradedLeibniz_completedDividedPowerOnRing p (A : Type u) _
    wedge_anti := completedDividedPowerWedgeOnRing_one_add_swap p (A : Type u) _
    deRham_diff := completedDividedPowerDeRham_one_differentialOnRing p (A : Type u) _
    psiA := completedMapDifferentialForms p (A : Type u) _ D'.dividedPowers
      (dpMorphismAlgHom a ha) a.isDPMorphism
    psiB := completedMapDifferentialForms p (A : Type u) D'.dividedPowers _
      (dpMorphismAlgHom b hb) b.isDPMorphism
    psiA_diff := completedMapDifferentialForms_differentialOnRing p (A : Type u) _ _ _ _
    psiB_diff := completedMapDifferentialForms_differentialOnRing p (A : Type u) _ _ _ _
    psiA_wedge := completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _
    psiB_wedge := completedMapDifferentialForms_wedge p (A : Type u) _ _ _ _
    psiA_deRham := completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _
    psiB_deRham := completedMapDifferentialForms_deRham p (A : Type u) _ _ _ _
    psiA_psiB := fun ω ↦ by
      have hc := completedMapDifferentialForms_comp p (A : Type u) D'.dividedPowers
        (envelopeCompletion E p hp).dividedPowers (dpMorphismAlgHom b hb) b.isDPMorphism
        D'.dividedPowers (dpMorphismAlgHom a ha) a.isDPMorphism (a.comp b).isDPMorphism 1 ω
      refine hc.symm.trans ?_
      exact (completedMapDifferentialForms_congr p (A : Type u) D'.dividedPowers D'.dividedPowers
        (g := AlgHom.id (A : Type u) (D' : Type u)) (AlgHom.ext hab) _
        (DPMorphism.id D'.dividedPowers).isDPMorphism 1 ω).trans
        (completedMapDifferentialForms_id p (A : Type u) D'.dividedPowers 1 _ ω)
    rho_sub_mem := hρ
    taylor := fun x n ↦ by
      obtain ⟨S, h1, h2, -⟩ := envelopeCompletion_taylor_levels E p hp
        (envelopeCompletionFormsBasis E p hp) (envelopeCompletionFormsBasis_apply E p hp) (b.comp a)
        (by ext c; exact (congrArg b (ha c)).trans (hb c)) hρ x n
      exact ⟨S, h1, h2⟩
    taylor' := fun x n ↦ by
      obtain ⟨S, h1, -, h3⟩ := envelopeCompletion_taylor_levels E p hp
        (envelopeCompletionFormsBasis E p hp) (envelopeCompletionFormsBasis_apply E p hp) (b.comp a)
        (by ext c; exact (congrArg b (ha c)).trans (hb c)) hρ x n
      exact ⟨S, h1, h3⟩ }

end Retract

end Crystalline

end
