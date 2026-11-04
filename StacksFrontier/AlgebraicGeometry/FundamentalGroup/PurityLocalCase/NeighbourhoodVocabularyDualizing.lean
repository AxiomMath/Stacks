module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.HypersurfaceExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitDualizingEquivalence

/-!
# Finite étale covers of a punctured hypersurface over a ring with a dualizing complex

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`.  Write `X = Spec A`, `X₀ = Spec (A / fA)`,
and let `U = X ∖ {𝔪}` and `U₀ = X₀ ∖ {𝔪}` be the two punctured spectra.  Assume

1. `A` has a dualizing complex and is `f`-adically complete,
2. one of
   * (a) `A_f` satisfies Serre's condition `(S₂)` and every irreducible component of `X` not
     contained in `X₀` has dimension at least `4`, or
   * (b) `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭 ∉ V(f)` whose closure meets `V(f)` in
     more than the closed point,
3. purity holds for `(A_f)_𝔭` at every maximal ideal `𝔭 ⊂ A_f`.

Then the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective; and if in addition
purity holds for `A`, then purity holds for `A / fA`.

Hypotheses (1) and (2) are exactly what makes the restriction functor
`colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⥤ FÉt_{U₀}` an equivalence, so a finite étale cover of `U₀` is
already defined over some open `U'` between `U₀` and `U`.  The points of `U` that `U'` omits are
maximal ideals of `A_f`, and hypothesis (3) extends the cover across them to a cover of `U`.
With purity for `A` the resulting cover of `U` extends over `X`, and the restriction of that
extension to `X₀` is the desired extension over `Spec (A / fA)`.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.exists_nbhd_finiteEtale_of_dualizing` — under (1)
  and (2), every finite étale cover of `U₀` is the restriction of a finite étale cover of an open
  `U'` of `X` with `U₀ ⊆ U' ⊆ U`.
* `AlgebraicGeometry.LocalLefschetzSituation.essSurj_finiteEtaleBaseChange_U₀ToU_of_dualizing`
  — under (1)–(3), the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective.
* `AlgebraicGeometry.LocalLefschetzSituation.hasPurity_quotientRing_of_dualizing` — under
  (1)–(3) together with purity for `A`, purity holds for `A / fA`.

## Implementation notes

The neighbourhoods of `U₀` in `U` are indexed here by the opens `U'` of `X` with `U₀ ⊆ U' ⊆ U`,
which is `AlgebraicGeometry.LocalLefschetzSituation.IsNeighbourhood`.  This is the canonical
indexing for the results of this chapter, because it is the one the extension of a cover across
the points of `U ∖ U'` is stated in: those points are points of `X`, and purity is applied at
their local rings.  The equivalence of the restriction functor out of the colimit is instead
proved for an ambient scheme carrying a quasi-coherent ideal sheaf, where a neighbourhood is an
open of the ambient scheme containing the support of the sheaf.  The two indexings are identified
once and for all by
`AlgebraicGeometry.LocalLefschetzSituation.exists_nbhd_finiteEtale_of_colimitEssSurj`, which
pushes an open of `U` forward along `U ⟶ X` and identifies `U₀` with the closed subscheme of `U`
cut out by the kernel of `U₀ ⟶ U`; everything below goes through it, and no other translation
between the two is used.

## References

* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 0DXY](https://stacks.math.columbia.edu/tag/0DXY)
* [Stacks Project, Tag 0EK9](https://stacks.math.columbia.edu/tag/0EK9)
* [Stacks Project, Tag 0DXZ](https://stacks.math.columbia.edu/tag/0DXZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (idealSheafNearVanishing)
open Stacks.FundamentalGroup (finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing)
open Stacks.LocalCohomology (complementZeroLocus)

universe u w

namespace AlgebraicGeometry

namespace LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-- **Every finite étale cover of `U₀` is defined over an open `U'` of `X` with
`U₀ ⊆ U' ⊆ U`.**  Assume `A` has a dualizing complex, is `f`-adically complete, and satisfies
hypothesis (2) of [Stacks, Tag 0DXY]: either `A_f` satisfies `(S₂)` and `dim(A/𝔭) ≥ 4` for every
minimal prime `𝔭` of `A` with `f ∉ 𝔭`, or `depth(A_𝔭) + dim(A/𝔭) > 3` for every prime `𝔭 ∉ V(f)`
whose closure meets `V(f)` in more than the closed point.  Then every finite étale cover of `U₀`
is isomorphic to the restriction of a finite étale cover of some open `U'` of `X` with
`U₀ ⊆ U' ⊆ U`.

This is the essential surjectivity half of [Stacks, Tag 0DXY], read in the indexing of the local
Lefschetz situation through
`AlgebraicGeometry.LocalLefschetzSituation.exists_nbhd_finiteEtale_of_colimitEssSurj`. -/
theorem exists_nbhd_finiteEtale_of_dualizing [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hcond :
      (PropertySkRing (Localization.Away S.f) 2 ∧
          ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → S.f ∉ p.asIdeal →
            (4 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
          ({q : PrimeSpectrum S.A | p.asIdeal ≤ q.asIdeal} ∩
            {q : PrimeSpectrum S.A | S.f ∈ q.asIdeal}) ≠
            {⟨maximalIdeal S.A, (maximalIdeal.isMaximal S.A).isPrime⟩} →
          (3 : WithBot ℕ∞) <
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
              ringKrullDim (S.A ⧸ p.asIdeal)))
    (C : FiniteEtaleOver S.U₀) :
    ∃ (W : S.X.Opens) (hW : S.IsNeighbourhood W) (B : FiniteEtaleOver W.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.nbhdRestriction hW)).obj B ≅ C) :=
  S.exists_nbhd_finiteEtale_of_colimitEssSurj
    (finiteEtaleColimitEquivalence_puncturedSpectrum_of_dualizing.{u, w} S.A S.f
      S.f_mem_maximalIdeal hdual hcomplete hcond).2 C

/-- **Stacks Project, Tag 0EK9.**  Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪`.
Write `X = Spec A`, let `U = X ∖ {𝔪}` and `U₀ = Spec (A / fA) ∖ {𝔪}` be the two punctured
spectra.  Assume

1. `A` has a dualizing complex and is `f`-adically complete,
2. one of
   * (a) `A_f` satisfies Serre's condition `(S₂)` and every irreducible component of `X` not
     contained in `V(f)` has dimension at least `4`, or
   * (b) `depth(A_𝔭) + dim(A/𝔭) > 3` whenever `𝔭 ∉ V(f)` and `V(𝔭) ∩ V(f) ≠ {𝔪}`,
3. purity holds for `(A_f)_𝔭` for every maximal ideal `𝔭 ⊂ A_f`.

Then the restriction functor `FÉt_U ⥤ FÉt_{U₀}` is essentially surjective.

The source's argument is followed.  Hypotheses (1) and (2) make the restriction functor
`colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⥤ FÉt_{U₀}` an equivalence, so a given finite étale cover of `U₀`
is already the restriction of a cover of some open `U'` of `X` with `U₀ ⊆ U' ⊆ U`.  The points of
`U` that `U'` omits correspond to maximal ideals of `A_f`, so hypothesis (3) makes purity
available at each of them and the cover extends from `U'` across them to a cover of `U`. -/
@[stacks 0EK9 "the restriction functor FÉt_U ⥤ FÉt_{U₀} is essentially surjective, under the \
tag's three hypotheses; nothing beyond them is assumed"]
theorem essSurj_finiteEtaleBaseChange_U₀ToU_of_dualizing
    [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hcond :
      (PropertySkRing (Localization.Away S.f) 2 ∧
          ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → S.f ∉ p.asIdeal →
            (4 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
          ({q : PrimeSpectrum S.A | p.asIdeal ≤ q.asIdeal} ∩
            {q : PrimeSpectrum S.A | S.f ∈ q.asIdeal}) ≠
            {⟨maximalIdeal S.A, (maximalIdeal.isMaximal S.A).isPrime⟩} →
          (3 : WithBot ℕ∞) <
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
              ringKrullDim (S.A ⧸ p.asIdeal)))
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p)) :
    (finiteEtaleBaseChange S.U₀ToU).EssSurj :=
  S.essSurj_finiteEtaleBaseChange_U₀ToU_of_forall_exists_nbhd haway
    (S.exists_nbhd_finiteEtale_of_dualizing.{u, w} hdual hcomplete hcond)

/-- **Stacks Project, Tag 0DXZ.**  Let `(A, 𝔪)` be a Noetherian local ring and let `f ∈ 𝔪`.
Write `X = Spec A`.  Assume

1. `A` has a dualizing complex and is `f`-adically complete,
2. one of
   * (a) `A_f` satisfies Serre's condition `(S₂)` and every irreducible component of `X` not
     contained in `V(f)` has dimension at least `4`, or
   * (b) `depth(A_𝔭) + dim(A/𝔭) > 3` whenever `𝔭 ∉ V(f)` and `V(𝔭) ∩ V(f) ≠ {𝔪}`,
3. purity holds for `(A_f)_𝔭` for every maximal ideal `𝔭 ⊂ A_f`, and
4. purity holds for `A`.

Then purity holds for `A / fA`.

The source's argument is followed.  A finite étale cover of the punctured spectrum `U₀` of
`A / fA` is, by the essential surjectivity of `FÉt_U ⥤ FÉt_{U₀}` under (1)–(3), the restriction
of a finite étale cover of the punctured spectrum `U` of `A`; hypothesis (4) extends the latter
over `X`; and the restriction of that extension to `Spec (A / fA)` is the desired extension of
the original cover. -/
@[stacks 0DXZ "purity for A/fA under the tag's four hypotheses; nothing beyond them is assumed"]
theorem hasPurity_quotientRing_of_dualizing [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hcond :
      (PropertySkRing (Localization.Away S.f) 2 ∧
          ∀ p : PrimeSpectrum S.A, IsMinimalPrime p.asIdeal → S.f ∉ p.asIdeal →
            (4 : WithBot ℕ∞) ≤ ringKrullDim (S.A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum S.A, S.f ∉ p.asIdeal →
          ({q : PrimeSpectrum S.A | p.asIdeal ≤ q.asIdeal} ∩
            {q : PrimeSpectrum S.A | S.f ∈ q.asIdeal}) ≠
            {⟨maximalIdeal S.A, (maximalIdeal.isMaximal S.A).isPrime⟩} →
          (3 : WithBot ℕ∞) <
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) +
              ringKrullDim (S.A ⧸ p.asIdeal)))
    (haway : ∀ (p : Ideal (Localization.Away S.f)) [p.IsMaximal],
      HasPurity (Localization.AtPrime p))
    (hpurity : HasPurity S.A) :
    HasPurity S.quotientRing :=
  S.hasPurity_quotientRing_of_essSurj_U₀ToU
    (S.essSurj_finiteEtaleBaseChange_U₀ToU_of_dualizing.{u, w} hdual hcomplete hcond haway)
    hpurity

end LocalLefschetzSituation

end AlgebraicGeometry

end
