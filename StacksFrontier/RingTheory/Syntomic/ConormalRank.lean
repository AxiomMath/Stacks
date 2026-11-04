module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.Homology.DoubleMappingCone
public import StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor
public import StacksFrontier.RingTheory.CompleteIntersection.CotangentDeterminant
public import StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.Syntomic.SquarePresentation
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
import all StacksFrontier.RingTheory.CompleteIntersection.NaiveCotangentPerfect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of the conormal module of a quasi-finite syntomic algebra

Let `B` be a quasi-finite syntomic algebra over `A` and let `B = A[x_1, …, x_n]/I` be a
presentation of `B` by `n` variables. Then the conormal module `I/I²` is finite locally free of
rank `n` at every prime of `B`. Consequently the naive cotangent complex `NL_{B/A}` has rank
zero: it is represented by the two-term complex `I/I² → ⨁ᵢ B dxᵢ` of finite projective modules
whose two terms have rank `n` at every prime.

## Main results

* `Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic`: the conormal module of a
  finite polynomial presentation of a quasi-finite syntomic algebra has rank the number of
  variables.
* `Algebra.Generators.exists_twoTermPresentation_naiveCotangentObject`: a finite polynomial
  presentation with finite projective conormal module gives a two-term presentation of
  `NL_{B/A}` whose terms have the ranks of `I/I²` and of `⨁ᵢ B dxᵢ`.
* `Algebra.isRankZero_naiveCotangentObject_of_quasiFinite_syntomic`: the naive cotangent complex
  of a quasi-finite syntomic algebra is a rank-zero perfect object of `D(B)`, in the sense of More
  on Algebra, Section 0FJI.

## Implementation notes

The rank is computed by comparing the given presentation with a *square* one. Near a prime `𝔮`
of `B` a syntomic algebra is a relative global complete intersection (Stacks 00SY), and
quasi-finiteness forces such a presentation to have as many relations as variables
(`Algebra.exists_square_presentation`); its conormal module is then free of rank the number of
variables (Stacks 00SV). Stacks 00S6 compares the two conormal modules up to free summands,
`(I/I²)_g ⊕ B_g^{⊕m} ≅ J/J² ⊕ B_g^{⊕n}`, and taking ranks at a prime of `B_g` over `𝔮` gives
`rank (I/I²) + m = m + n`. The conormal module of the given presentation is finite flat by
Stacks 08RK, which is what makes the rank additive along the two direct sums.

Rank zero of `NL_{B/A}` is read on the two-term presentation that Stacks 0FV0 uses for
perfectness: the mapping cone of `I/I² → ⨁ᵢ B dxᵢ` for a finite presentation, which computes the
canonical naive cotangent complex by Stacks 00S1 (4). Its term in degree `-1` is the conormal
module, of rank `n` by the above, and its term in degree `0` is free on the `n` differentials.

## References

* [Stacks Project, Tag 00S6](https://stacks.math.columbia.edu/tag/00S6)
* [Stacks Project, Tag 00SV](https://stacks.math.columbia.edu/tag/00SV)
* [Stacks Project, Tag 00SY](https://stacks.math.columbia.edu/tag/00SY)
* [Stacks Project, Tag 08RK](https://stacks.math.columbia.edu/tag/08RK)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- The conormal module of any finite polynomial presentation of a syntomic algebra is finite
projective. -/
private theorem cotangent_finite_projective_of_syntomic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B] {n : ℕ}
    (P : Algebra.Generators A B (Fin n)) :
    Module.Finite B P.toExtension.Cotangent ∧ Module.Projective B P.toExtension.Cotangent :=
  P.cotangent_finite_projective_of_isLocalCompleteIntersection
    ((NaiveCotangent.hasTorAmplitude_tfae_syntomic A B (Algebra.Syntomic A B) (by simp)
      (RingHom.IsLocalCompleteIntersection (algebraMap A B)) (by simp)).mp
      ‹Algebra.Syntomic A B›)

/-- **The conormal module of a quasi-finite syntomic algebra has rank the number of variables.**
If `B = A[x_1, …, x_n]/I` is quasi-finite and syntomic over `A`, then the conormal module `I/I²`
has rank `n` at every prime of `B`. -/
theorem Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] {n : ℕ}
    (P : Algebra.Generators A B (Fin n)) (q : PrimeSpectrum B) :
    Module.rankAtStalk P.toExtension.Cotangent q = n := by
  -- the conormal module of `P` is finite and flat over `B`
  obtain ⟨_, _⟩ := cotangent_finite_projective_of_syntomic P
  -- a relative global complete intersection after inverting one element away from `𝔮`
  obtain ⟨hflat, hci⟩ := Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber
    (R := A) (S := B) q.asIdeal
  have := hflat
  obtain ⟨g, hg, hgci⟩ := Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat
    (R := A) q.asIdeal hci
  have := hgci
  -- the prime of `B_g` over `𝔮`
  obtain ⟨qT, hqT⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge
    ((PrimeSpectrum.mem_basicOpen g q).mpr hg)
  -- a square presentation of `B_g` over `A`
  obtain ⟨m, Q, hQ⟩ := Algebra.exists_square_presentation (R := A)
    (S := Localization.Away g) qT.asIdeal
  have := hQ
  obtain ⟨b, -⟩ := Q.exists_basis_cotangent_relation
  -- Stacks 00S6 for the two presentations
  obtain ⟨e⟩ :=
    Algebra.Generators.nonempty_cotangent_baseChange_prod_linearEquiv_of_isLocalizationAway
      (R := A) (T := Localization.Away g) g P Q.toGenerators
  -- `B_g` is nontrivial, carrying the prime `qT`
  have := qT.nontrivial
  have hm : Module.rankAtStalk (R := Localization.Away g)
      (Fin m → Localization.Away g) qT = m := by simp
  have hn : Module.rankAtStalk (R := Localization.Away g)
      (Fin n → Localization.Away g) qT = n := by simp
  have hQ' : Module.rankAtStalk Q.toExtension.Cotangent qT = m := by
    simp [Module.finrank_eq_card_basis b]
  have key := congrFun (Module.rankAtStalk_eq_of_equiv e) qT
  simp only [Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_baseChange, hqT, hm, hn,
    hQ'] at key
  omega

open CategoryTheory in
/-- **The two-term presentation of `NL_{B/A}` attached to a finite polynomial presentation.** If
`B = A[x_1, …, x_n]/I` has finite projective conormal module `I/I²`, then `NL_{B/A}` admits a
two-term presentation by finite projective modules whose term in degree `-1` has the rank of
`I/I²` and whose term in degree `0` has rank `n`, at every prime of `B`.

It is the presentation of Stacks 0FV0, the mapping cone of `I/I² → ⨁ᵢ B dxᵢ`, which computes
the canonical naive cotangent complex by Stacks 00S1 (4). -/
theorem Algebra.Generators.exists_twoTermPresentation_naiveCotangentObject
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (P : Algebra.Generators A B (Fin n)) [Module.Finite B P.toExtension.Cotangent]
    [Module.Projective B P.toExtension.Cotangent] :
    ∃ T : TwoTermDeterminant.TwoTermPresentation (NaiveCotangent.naiveCotangentObject A B),
      ∀ q : PrimeSpectrum B,
        Module.rankAtStalk (T.complex.X (-1)) q =
            Module.rankAtStalk P.toExtension.Cotangent q ∧
          Module.rankAtStalk (T.complex.X 0) q = n := by
  classical
  have : Module.Finite B P.toExtension.CotangentSpace :=
    Module.Finite.of_basis P.cotangentSpaceBasis
  have : Module.Projective B P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  let E : ULift.{u} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent :=
    ULift.moduleEquiv
  let d := P.toExtension.cotangentComplex.comp E.toLinearMap
  obtain ⟨hGE, hLE, hfinite, hprojective⟩ := NaiveCotangent.twoTermComplex_finite_projective d
  let P' := NaiveCotangent.canonicalGenerators A B
  obtain ⟨e⟩ := NaiveCotangent.twoTermComplex_iso_of_homotopyEquiv
    (NaiveCotangent.NL P) (NaiveCotangent.NL P') (NaiveCotangent.nlMap P P' (P.defaultHom P'))
    (NaiveCotangent.nlMap_isHomotopyEquiv_and_isQuasiIso
      (R := A) (R' := A) (S := B) (S' := B)
      (by simpa using Function.bijective_id) (by simpa using Function.bijective_id)
      P P' (P.defaultHom P')).1
  refine ⟨⟨_, hfinite, hprojective, hGE, hLE, e.symm⟩, fun q => ⟨?_, ?_⟩⟩
  · exact (congrFun (Module.rankAtStalk_eq_of_equiv
      (HomologicalComplex.singleConeNegOneIso (ModuleCat.ofHom d)).toLinearEquiv) q).symm.trans
      (congrFun (Module.rankAtStalk_eq_of_equiv E) q)
  · have h₀ := congrFun (Module.rankAtStalk_eq_of_equiv
      (HomologicalComplex.singleConeZeroIso (ModuleCat.ofHom d)).toLinearEquiv) q
    have := q.nontrivial
    have hS : Module.rankAtStalk P.toExtension.CotangentSpace q = n := by
      simp [Module.finrank_eq_card_basis P.cotangentSpaceBasis]
    exact h₀.symm.trans hS

/-- **The naive cotangent complex of a quasi-finite syntomic algebra has rank zero.** If `B` is
quasi-finite and syntomic over `A`, then `NL_{B/A}` admits a two-term presentation
`I/I² → ⨁ᵢ B dxᵢ` by finite projective modules of equal rank at every prime of `B`.

The presentation is the one of Stacks 0FV0 attached to a finite presentation
`B = A[x_1, …, x_n]/I`: its conormal term has rank `n` by
`Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic`, and its cotangent-space term is
free on the `n` differentials `dxᵢ`. -/
@[sga "6 0 4.4" "special case"]
theorem Algebra.isRankZero_naiveCotangentObject_of_quasiFinite_syntomic
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Syntomic A B] [Algebra.QuasiFinite A B] :
    TwoTermDeterminant.IsRankZero (NaiveCotangent.naiveCotangentObject A B) := by
  classical
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Algebra.Generators A B (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rwa [heval])
  obtain ⟨_, _⟩ := cotangent_finite_projective_of_syntomic P
  obtain ⟨T, hT⟩ := P.exists_twoTermPresentation_naiveCotangentObject
  exact ⟨T, fun q => (hT q).1.trans
    ((Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic P q).trans (hT q).2.symm)⟩
