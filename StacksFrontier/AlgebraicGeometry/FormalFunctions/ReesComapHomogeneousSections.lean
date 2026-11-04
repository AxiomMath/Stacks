module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapLocallySurjective

/-!
# The Rees comparison on a homogeneous element of the Rees algebra

Let `A` be a ring, `I ⊆ A` an ideal, `B = reesAlgebra I` its Rees algebra and `g : Z ⟶ Spec A`
a morphism of schemes. [Stacks, Tag 0897]'s base change needs the ring map
`B →+* Γ(Z, ⨁ₙ (I𝒪_Z)ⁿ)` obtained by evaluating the comparison of
`StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapAlgebraSheaf`, and that map is only
usable once one knows what it does to a *homogeneous* element of `B`.

`Stacks.Blowup.reesComapSections_ungradedIncl`
(`StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapLocallySurjective`) already evaluates
the comparison on a section of the form `ungradedIncl k x`. What was missing, and is supplied
here, is the other half: the identification of `Γ(Spec A, B̃) ≅ B` carries a homogeneous element
of `B` of degree `k` to a section of that form, so that the first lemma applies to it.

## Main results

* `Stacks.Blowup.reesSectionsRingEquiv_coe_reesGrading`: **over an affine open `U`, the
  identification `reesAlgebra ℐ(U) ≅ Γ(U, ⨁ₙ ℐⁿ)` carries a homogeneous element of degree `k` to
  the degree-`k` inclusion of the homogeneous section with the matching ambient section.** The
  hypothesis is phrased through `Stacks.Blowup.reesPieceAmbient`, which determines a homogeneous
  section in nonnegative degree (`Stacks.Blowup.reesPieceAmbient_injective`), so the statement
  applies to whichever concrete section one has a formula for.
* `Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv_coe_reesGrading` and
  `Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv_reesGrading`: the same statement at
  `Γ(Spec A, B̃) ≅ reesAlgebra I`, the second one at the named section
  `Stacks.Cohomology.FormalFunctions.specReesSection`.
* `Stacks.Cohomology.FormalFunctions.reesComapSections_specReesSectionsEquiv`: **the two halves
  composed** — the comparison on global sections carries a homogeneous element `b` of degree `k`
  of `reesAlgebra I` to the degree-`k` inclusion of the inverse image of the section attached
  to `b`.

## Implementation notes

The identification `Stacks.Blowup.reesSectionsRingEquiv` is a fourfold composite: the ordinary
Rees algebra is the graded section ring of `AlgebraicGeometry.reesSituation`
(`AlgebraicGeometry.reesSectionRingEquiv`), that situation agrees with the explicitly built one
(`Stacks.Blowup.ReesModel.sectionRingEquiv`), the `ℕ`-indexed section ring is the `ℤ`-indexed
ungraded realization (`Stacks.RelativeProj.Situation.sectionRingTotalEquiv`), and over an affine
open the sheafification changes nothing (`Stacks.RelativeSpec.totalSectionsRingEquiv`). Each
factor is computed on a homogeneous element by its own `_of` lemma; the proof below is that
computation, written with `Eq.trans` and `congrArg` rather than `rw` for the reason recorded in
the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapAlgebraSheaf`.

The transport of the Rees algebra along `Γ(Spec A, ⊤) ≅ A` is computed degreewise by
`Stacks.Blowup.coe_reesGradingEquivPow_symm_reesAlgebraCongr`: on coefficients it is the ring
isomorphism itself, so the ambient section of the resulting homogeneous section is the image of
`Stacks.Cohomology.FormalFunctions.reesElt`.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Blowup Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology
open Stacks.RelativeProj

universe u

namespace Stacks.Blowup

/-! ### Transport of a homogeneous element along a ring isomorphism -/

variable {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R')

/-- The transport of the Rees algebra along a ring isomorphism preserves degrees: applying `e`
to the coefficients does not move the support of a polynomial. -/
theorem reesAlgebraCongr_mem_reesGrading {I : Ideal R} {J : Ideal R'}
    (h : J = I.map (e : R →+* R')) {k : ℕ} (b : ↥(reesGrading I k)) :
    reesAlgebraCongr e h (b : ↥(reesAlgebra I)) ∈ reesGrading J k := by
  intro i hi
  show (((b : ↥(reesAlgebra I)) : Polynomial R).map (e : R →+* R')).coeff i = 0
  rw [Polynomial.coeff_map, b.2 i hi, map_zero]

/-- **The transport of the Rees algebra along a ring isomorphism is `e` on the degree-`k`
coefficient**, the degree-`k` part of either Rees algebra being the corresponding power of the
ideal. -/
theorem coe_reesGradingEquivPow_symm_reesAlgebraCongr {I : Ideal R} {J : Ideal R'}
    (h : J = I.map (e : R →+* R')) {k : ℕ} (b : ↥(reesGrading I k)) :
    ((reesGradingEquivPow J k).symm
        ⟨reesAlgebraCongr e h (b : ↥(reesAlgebra I)),
          reesAlgebraCongr_mem_reesGrading e h b⟩ : R') =
      e ((reesGradingEquivPow I k).symm b : R) := by
  rw [coe_reesGradingEquivPow_symm, coe_reesGradingEquivPow_symm]
  exact Polynomial.coeff_map _ _

/-! ### The sections of `⨁ₙ ℐⁿ` on a homogeneous element -/

/-- **Over an affine open, the identification of the sections of `⨁ₙ ℐⁿ` with the ordinary Rees
algebra of `ℐ(U)` (`Stacks.Blowup.reesSectionsRingEquiv`) carries a homogeneous element of degree
`k` to the degree-`k` inclusion of a homogeneous section.**

The section in question is pinned down by its ambient section
(`Stacks.Blowup.reesPieceAmbient_injective`), which is the degree-`k` coefficient of the
homogeneous element; stating the hypothesis that way lets the lemma be applied to whichever
concrete section is at hand. This is the homogeneous counterpart of
`Stacks.Blowup.reesSectionsRingEquiv_algebraMap`, which is the degree-zero case. -/
theorem reesSectionsRingEquiv_coe_reesGrading {X : Scheme.{u}} (J : X.IdealSheafData)
    (U : X.affineOpens) (k : ℕ) (c : ↥(reesGrading (J.ideal U) k))
    (σ : (reesPiece J (k : ℤ)).val.obj (op U.1))
    (hσ : reesPieceAmbient J (k : ℤ) U.1 σ =
      ((reesGradingEquivPow (J.ideal U) k).symm c : Γ(X, U.1))) :
    reesSectionsRingEquiv J U (c : ↥(reesAlgebra (J.ideal U))) =
      (reesGradedAlgebra J).ungradedIncl (k : ℤ) σ := by
  have h1 : (AlgebraicGeometry.reesSectionRingEquiv J U) (DirectSum.of
        ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) k
        ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c)) =
      (c : ↥(reesAlgebra (J.ideal U))) :=
    (AlgebraicGeometry.reesSectionToAddHom_of J U k _).trans
      (congrArg (fun z : ↥(reesGrading (J.ideal U) k) => (z : ↥(reesAlgebra (J.ideal U))))
        ((AlgebraicGeometry.reesGradedPieceEquiv J U k).apply_symm_apply c))
  have h1' : (AlgebraicGeometry.reesSectionRingEquiv J U).symm
        (c : ↥(reesAlgebra (J.ideal U))) =
      DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) k
        ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c) := by
    rw [← h1, RingEquiv.symm_apply_apply]
  have hpe : ((AlgebraicGeometry.reesPieceEquiv J U k)
        ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c) : Γ(X, U.1)) =
      ((reesGradingEquivPow (J.ideal U) k).symm c : Γ(X, U.1)) :=
    congrArg (fun z : ↥(J.ideal U ^ k) => (z : Γ(X, U.1)))
      ((AlgebraicGeometry.reesPieceEquiv J U k).apply_symm_apply _)
  have hσ₀ : σ = ((reesSituationModel J).compare U k).symm
      ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c) := by
    refine reesPieceAmbient_injective J (k : ℤ) (Int.natCast_nonneg k) U.1 (hσ.trans ?_)
    refine hpe.symm.trans (Eq.trans ?_
      (((reesSituationModel J).coe_reesPieceEquiv_compare U k _).trans
        (reesPieceAffineEquiv_coe J (k : ℤ) (Int.natCast_nonneg k) U _)))
    exact congrArg (fun z => ((AlgebraicGeometry.reesPieceEquiv J U k z) : Γ(X, U.1)))
      (((reesSituationModel J).compare U k).apply_symm_apply _).symm
  have hs : ((reesSituationModel J).sectionRingEquiv U).symm
        (DirectSum.of ((AlgebraicGeometry.reesSituation J).sectionPieces U.1) k
          ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c)) =
      DirectSum.of ((reesSituation J).sectionPieces U.1) k
        (((reesSituationModel J).compare U k).symm
          ((AlgebraicGeometry.reesGradedPieceEquiv J U k).symm c)) :=
    (reesSituationModel J).sectionInv_of U k _
  refine Eq.trans ?_ (congrArg ((reesGradedAlgebra J).ungradedIncl (k : ℤ)) hσ₀).symm
  change Stacks.RelativeSpec.totalSectionsRingEquiv X (reesGradedAlgebra J)
      (fun i j W a b => reesMultiplication_comm J i j W a b) U.2
      (Situation.sectionRingTotalEquiv (reesSituation J) U.1
        (((reesSituationModel J).sectionRingEquiv U).symm
          ((AlgebraicGeometry.reesSectionRingEquiv J U).symm
            (c : ↥(reesAlgebra (J.ideal U)))))) = _
  rw [h1', hs]
  exact congrArg _ (Situation.sectionRingToTotal_of (reesSituation J) U.1 k _)

end Stacks.Blowup

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `Γ(Spec A, B̃) ≅ reesAlgebra I` on a homogeneous element -/

/-- The image in `Γ(Spec A, ⊤)` of the element of `Iᵏ` underlying a homogeneous element of degree
`k` of `B = reesAlgebra I` lies in `Ĩ(Spec A)ᵏ`. -/
theorem specTopEquiv_reesElt_mem (k : ℕ) (b : ↥(reesGrading I k)) :
    specTopEquiv (reesElt I b) ∈
      (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ ^ k := by
  rw [specIdealSheaf_ideal_top, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (reesElt_mem I b)

/-- **The global section of `Ĩᵏ` attached to a homogeneous element of degree `k` of
`B = reesAlgebra I`**: the section of the degree-`k` piece of `B̃` over `Spec A` whose ambient
section is the image of `Stacks.Cohomology.FormalFunctions.reesElt`. Over the affine `Spec A`
such a section exists and is unique (`Stacks.Blowup.reesPieceAffineEquiv`). -/
def specReesSection (k : ℕ) (b : ↥(reesGrading I k)) :
    (reesPiece (specIdealSheaf I) (k : ℤ)).val.obj (op (⊤ : (Spec (.of A)).Opens)) :=
  (reesPieceAffineEquiv (specIdealSheaf I) (k : ℤ) (Int.natCast_nonneg k)
      ⟨⊤, isAffineOpen_top (Spec (.of A))⟩).symm
    ⟨specTopEquiv (reesElt I b), specTopEquiv_reesElt_mem I k b⟩

/-- The ambient section of `Stacks.Cohomology.FormalFunctions.specReesSection`, which is what
pins it down. -/
theorem reesPieceAmbient_specReesSection (k : ℕ) (b : ↥(reesGrading I k)) :
    reesPieceAmbient (specIdealSheaf I) (k : ℤ) ⊤ (specReesSection I k b) =
      specTopEquiv (reesElt I b) :=
  (reesPieceAffineEquiv_coe (specIdealSheaf I) (k : ℤ) (Int.natCast_nonneg k)
      ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ _).symm.trans
    (congrArg (fun z : ↥((specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ ^ k) =>
        (z : Γ(Spec (.of A), ⊤)))
      ((reesPieceAffineEquiv (specIdealSheaf I) (k : ℤ) (Int.natCast_nonneg k)
        ⟨⊤, isAffineOpen_top (Spec (.of A))⟩).apply_symm_apply _))

/-- **`Γ(Spec A, B̃) ≅ reesAlgebra I` carries a homogeneous element of degree `k` to the
degree-`k` inclusion of a homogeneous global section.** The section is determined by its ambient
section, which is the image in `Γ(Spec A, ⊤)` of the element of `Iᵏ` underlying the homogeneous
element. This is the homogeneous counterpart of
`Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv_algebraMap`. -/
theorem specReesSectionsEquiv_coe_reesGrading (k : ℕ) (b : ↥(reesGrading I k))
    (σ : (reesPiece (specIdealSheaf I) (k : ℤ)).val.obj (op (⊤ : (Spec (.of A)).Opens)))
    (hσ : reesPieceAmbient (specIdealSheaf I) (k : ℤ) ⊤ σ = specTopEquiv (reesElt I b)) :
    specReesSectionsEquiv I (b : ↥(reesAlgebra I)) =
      (reesGradedAlgebra (specIdealSheaf I)).ungradedIncl (k : ℤ) σ := by
  refine Eq.trans (show specReesSectionsEquiv I (b : ↥(reesAlgebra I)) =
    reesSectionsRingEquiv (specIdealSheaf I) ⟨⊤, isAffineOpen_top (Spec (.of A))⟩
      ((⟨reesAlgebraCongr (specTopEquiv (A := A)) (specIdealSheaf_ideal_top I)
            (b : ↥(reesAlgebra I)),
          reesAlgebraCongr_mem_reesGrading (specTopEquiv (A := A))
            (specIdealSheaf_ideal_top I) b⟩ :
        ↥(reesGrading ((specIdealSheaf I).ideal
          ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) k)) :
      ↥(reesAlgebra ((specIdealSheaf I).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of A))⟩))) from rfl) ?_
  refine reesSectionsRingEquiv_coe_reesGrading (specIdealSheaf I)
    ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ k _ σ (hσ.trans ?_)
  exact (coe_reesGradingEquivPow_symm_reesAlgebraCongr (specTopEquiv (A := A))
    (specIdealSheaf_ideal_top I) b).symm

/-- `Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv_coe_reesGrading` at the named
section. -/
theorem specReesSectionsEquiv_reesGrading (k : ℕ) (b : ↥(reesGrading I k)) :
    specReesSectionsEquiv I (b : ↥(reesAlgebra I)) =
      (reesGradedAlgebra (specIdealSheaf I)).ungradedIncl (k : ℤ) (specReesSection I k b) :=
  specReesSectionsEquiv_coe_reesGrading I k b _ (reesPieceAmbient_specReesSection I k b)

/-! ### The two halves composed -/

/-- **The comparison `β` of [Stacks, Tag 01OG] on global sections, evaluated at a homogeneous
element of the Rees algebra of the base.** This is
`Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv_reesGrading` followed by
`Stacks.Blowup.reesComapSections_ungradedIncl`, and it is the computation
[Stacks, Tag 0897]'s base change needs of the ring map `reesAlgebra I →+* Γ(Z, ⨁ₙ (I𝒪_Z)ⁿ)`. -/
theorem reesComapSections_specReesSectionsEquiv {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A)) (k : ℕ)
    (b : ↥(reesGrading I k)) :
    reesComapSections g (specIdealSheaf I) (specReesSectionsEquiv I (b : ↥(reesAlgebra I))) =
      (reesGradedAlgebra ((specIdealSheaf I).comap g)).ungradedIncl (k : ℤ)
        ((reesPieceComap g (specIdealSheaf I) (k : ℤ)).val.app (op ⊤) (specReesSection I k b)) :=
  (congrArg (fun z => reesComapSections g (specIdealSheaf I) z)
      (specReesSectionsEquiv_reesGrading I k b)).trans
    (reesComapSections_ungradedIncl g (specIdealSheaf I) (k : ℤ) (specReesSection I k b))

end Stacks.Cohomology.FormalFunctions

end
