module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticProIsomorphismLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticQuasiCoherentLinearEquivalence
public import StacksFrontier.RingTheory.Koszul.KoszulTateSystemProIso

/-!
# The quotient tower and the Koszul tower have equivalent quasi-coherent categories

Let `f₁, …, f_r` be a weakly proregular sequence in a commutative ring `R` generating the ideal
`I`. Steps (1)–(3) of the proof of Proposition 0GZK, which Remark 0H1E carries over from the
Noetherian case, show that the categories `QC(𝒜)` and `QC(ℬ)` of the sheaves `𝒜 = (R / I ^ n)` and
`ℬ = (K_n)` (Koszul algebras on `f₁ ^ n, …, f_r ^ n`) on `ℕ` with the chaotic topology are
equivalent. The equivalence is the composite of

* `QC(𝒜) ≃ QC(𝒜')`, `𝒜' = (R / (f₁ ^ n, …, f_r ^ n))`, along the pro-isomorphism of the two
  quotient towers (Lemma 0GZH, step (3));
* `QC(𝒜') ≃ QC(𝒜'ₑ)`, along the subsystem over the exponents `nᵢ` of the Koszul–Tate ladder;
* `QC(𝒜'ₑ) ≃ QC(ℰ)` for the Tate system `ℰ = (Eᵢ)`, along the quasi-isomorphism `ℰ → 𝒜'ₑ`
  (Lemma 0GZF, step (2));
* `QC(ℰ) ≃ QC(ℬₑ) ≃ QC(ℬ)`, along the pro-isomorphisms of Remark 0GZ5 (Lemma 0GZH, step (1));

each an equivalence of `R`-linear triangulated categories. The site is `Stacks.LiftedNat.{u}`.

## Main definitions

* `Koszul.idealPowKoszulQCEquivalence`: **the equivalence `QC(𝒜) ≃ QC(ℬ)` of `R`-linear
  triangulated categories, for a weakly proregular sequence.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory SheafOfModules.DifferentialGradedModule DividedPowers.TateResolution

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The quasi-coherent categories of the quotient tower `(R / I ^ n)` and of the Koszul tower
`(K_n)` of a weakly proregular sequence `f` generating `I` are equivalent as `R`-linear
triangulated categories**: steps (1)–(3) of the proof of Proposition 0GZK, in the generality of
Remark 0H1E. -/
def idealPowKoszulQCEquivalence (f : Fin r → R) (proregular : IsWeaklyProregular f) :
    LinearTriangulatedEquivalence R
      (Chaotic.QC (liftedIdealPowSheafAlgebra.{u} (Ideal.span (Set.range f)))).FullSubcategory
      (Chaotic.QC (liftedPowSheafAlgebra.{u} f)).FullSubcategory :=
  (liftedPowQuotientIdealPowProIso f).qcLinearTriangulatedEquivalence.symm.trans <|
  (liftedKoszulTateQuotientSeqProIso f proregular).qcLinearTriangulatedEquivalence.trans <|
  (Chaotic.qcDerivedExtensionLinearTriangulatedEquivalence (liftedKoszulTateAugHom f proregular)
    (liftedKoszulTateAugHom_preservesOne f proregular)
    (isQuasiIso_liftedKoszulTateAugHom f proregular)).symm.trans <|
  (liftedKoszulTateProIso f proregular).qcLinearTriangulatedEquivalence.symm.trans
    (liftedKoszulTateKoszulSeqProIso f proregular).qcLinearTriangulatedEquivalence.symm

end Koszul
