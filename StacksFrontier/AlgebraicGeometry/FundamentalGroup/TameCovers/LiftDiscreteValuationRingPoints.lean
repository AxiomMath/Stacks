module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameCovers.DiscreteValuationRingPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOnePullbackRamification
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting points over discrete valuation rings to the normalization of a tame cover

[Stacks, Tag 0EYI]: let `X` be a locally Noetherian scheme, `D ⊆ X` an effective Cartier divisor
which is a regular scheme, and `Y ⟶ X ∖ D` a finite étale morphism tamely ramified over `X` in
codimension one (the situation of [Stacks, Tag 0EYG]); let `π : Y' ⟶ X` be the normalization of
`X` in `Y` ([Stacks, Tag 0EYH]). Let `R` be a discrete valuation ring with fraction field `K` and
`t : Spec R ⟶ X` a morphism with `t⁻¹D` the reduced closed point of `Spec R`.
1. If `t|_{Spec K}` lifts to `Y`, then `t` lifts to `t' : Spec R ⟶ Y'` and `π` is étale along
   `t'(Spec R)`.
2. If `Spec K ×_X Y` is a disjoint union of copies of `Spec K`, then `π` is finite étale over an
   open neighbourhood of `t(Spec R)`.

The proofs are `AlgebraicGeometry.TameCovers.exists_lift_etaleAt_fromNormalization` and
`AlgebraicGeometry.TameCovers.exists_opens_etale_fromNormalization`, whose named argument is
supplied by a proved theorem: the tame half of [Stacks, Tag 0EYD]
(`Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne`).

## Main results

* `AlgebraicGeometry.TameCovers.exists_lift_etaleAt_fromNormalization_of_isTamelyRamified`:
  Tag 0EYI (1).
* `AlgebraicGeometry.TameCovers.exists_opens_etale_fromNormalization_of_isTamelyRamified`:
  Tag 0EYI (2).

## References

* [Stacks Project, Tag 0EYI](https://stacks.math.columbia.edu/tag/0EYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TameCovers

/-- **Stacks Project, Tag 0EYI (1).** Let `X` be a locally Noetherian scheme, `D ⊆ X` an
effective Cartier divisor such that `D` is a regular scheme, and `f : Y ⟶ X ∖ D` a finite étale
morphism tamely ramified over `X` in codimension one (the situation of [Stacks, Tag 0EYG]). Let
`π : Y' ⟶ X` be the normalization of `X` in `Y` ([Stacks, Tag 0EYH]). Let `R` be a discrete
valuation ring with fraction field `K` and `t : Spec R ⟶ X` a morphism such that the scheme
theoretic inverse image `t⁻¹D` is the reduced closed point of `Spec R`. If `t|_{Spec K}` lifts to
a point `y : Spec K ⟶ Y`, then there is a lift `t' : Spec R ⟶ Y'` of `t` (extending `y`) such
that `π` is étale along `t'(Spec R)`.

Here `D` is the closed subscheme `D.subscheme` cut out by the ideal sheaf `D`, `X ∖ D` is the
open subscheme `D.support.compl`, and `Y'` is the relative normalization of `Y ⟶ X`. -/
@[stacks 0EYI "(1): a lift of `t|_{Spec K}` to `Y` gives a lift `t'` of `t` to the \
normalization `Y'`, and `Y' ⟶ X` is étale along `t'(Spec R)`"]
theorem exists_lift_etaleAt_fromNormalization_of_isTamelyRamified
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hDreg : IsRegular D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : Spec (.of R) ⟶ X)
    (ht : D.comap t = Scheme.IdealSheafData.vanishingIdeal
      ⟨({IsLocalRing.closedPoint R} : Set (Spec (.of R))),
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
          (IsLocalRing.maximalIdeal.isMaximal R)⟩)
    (y : Spec (.of K) ⟶ Y)
    (hy : y ≫ f ≫ Scheme.Opens.ι (D.support.compl : X.Opens) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t) :
    ∃ t' : Spec (.of R) ⟶ (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).normalization,
      t' ≫ (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization = t ∧
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t' =
        y ≫ (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).toNormalization ∧
      ∀ r, EtaleAt (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization (t' r) := by
  have hreg := (isRegular_tfae D.subscheme).out 1 2
  exact exists_lift_etaleAt_fromNormalization
    (fun S h ↦ Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne S h)
    D hD (hreg.mp hDreg).2 f hf R K t ht y hy

/-- **Stacks Project, Tag 0EYI (2).** In the situation of Tag 0EYI (1) (`X` locally Noetherian,
`D ⊆ X` an effective Cartier divisor which is a regular scheme, `f : Y ⟶ X ∖ D` finite étale and
tamely ramified over `X` in codimension one, `π : Y' ⟶ X` the normalization of `X` in `Y`, `R` a
discrete valuation ring with fraction field `K`, `t : Spec R ⟶ X` with `t⁻¹D` the reduced closed
point of `Spec R`): if `Spec K ×_X Y` is isomorphic, over `Spec K`, to a disjoint union of copies
of `Spec K`, then `π` is finite étale over an open neighbourhood `V` of `t(Spec R)`. -/
@[stacks 0EYI "(2): if `Spec K ×_X Y` is a disjoint union of copies of `Spec K`, the \
normalization `Y' ⟶ X` is finite étale over an open neighbourhood of `t(Spec R)`"]
theorem exists_opens_etale_fromNormalization_of_isTamelyRamified
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (hDreg : IsRegular D.subscheme)
    {Y : Scheme.{u}} (f : Y ⟶ (D.support.compl : X.Opens)) [IsFinite f] [Etale f]
    (hf : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (D.support.compl : X.Opens)) f)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : Spec (.of R) ⟶ X)
    (ht : D.comap t = Scheme.IdealSheafData.vanishingIdeal
      ⟨({IsLocalRing.closedPoint R} : Set (Spec (.of R))),
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
          (IsLocalRing.maximalIdeal.isMaximal R)⟩)
    (J : Type u)
    (eJ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t)
        (f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)) ≅ ∐ fun _ : J ↦ Spec (.of K))
    (heJ : eJ.hom ≫ Sigma.desc (fun _ ↦ 𝟙 _) = pullback.fst _ _) :
    ∃ V : X.Opens, (∀ r, t r ∈ V) ∧
      IsFinite ((f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization ∣_ V) ∧
      Etale ((f ≫ Scheme.Opens.ι (D.support.compl : X.Opens)).fromNormalization ∣_ V) := by
  have hreg := (isRegular_tfae D.subscheme).out 1 2
  exact exists_opens_etale_fromNormalization
    (fun S h ↦ Stacks.FundamentalGroup.pulledBackCover_isTamelyRamifiedInCodimensionOne S h)
    D hD (hreg.mp hDreg).2 f hf R K t ht J eJ heJ

end AlgebraicGeometry.TameCovers

end
