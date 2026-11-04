module

public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.StageFactorization
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.Retraction
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.ProductSplitting
public import StacksFrontier.RingTheory.SpreadingOut.LocalIsomorphism.AwayIsomorphism

/-!
# Local isomorphisms of algebras of finite presentation

Let `φ : R → S` be a ring map of finite presentation and let `q ⊆ S` be a prime lying over
`p ⊆ R` such that the induced map `R_p → S_q` is an isomorphism. Then there are `f ∈ R`, `f ∉ p`,
and an `R_f`-algebra `C` with `S_f ≅ R_f × C` as `R_f`-algebras. Moreover, if `S` and `S'` are
`R`-algebras of finite presentation and `q ⊆ S`, `q' ⊆ S'` are primes with `S_q ≅ S'_{q'}` as
`R`-algebras, then there are `g ∈ S`, `g ∉ q` and `g' ∈ S'`, `g' ∉ q'` with `S_g ≅ S'_{g'}` as
`R`-algebras.

## Main results

* `exists_away_prod_of_localRingHom_bijective`: if `R_p → S_q` is bijective, then
  `S_f ≅ R_f × C` as `R_f`-algebras for some `f ∉ p` and some `R_f`-algebra `C`.
* `exists_algEquiv_prod_of_isIdempotentElem`: an `R`-algebra `A` with an idempotent `g` such
  that `A ⧸ (1 - g) ≅ R` is isomorphic to a product `R × C`.
* `Stacks.SpreadingOut.LocalIsoSplitting.exists_mem_algHom_localizationAway_of_finitePresentation`:
  for `S` of finite presentation over `R`, every `R`-algebra map from `S` to a localization `Tₘ`
  of `T` at `M` factors through the localization of `T` away from a single element of `M`.
* `exists_notMem_algEquiv_localizationAway_of_isLocalization_atPrime`, in the namespace
  `Stacks.SpreadingOut.LocalIsoSplitting`: if `A` is of finite presentation over `B` and
  `B_p → A_Q` is an isomorphism, then `A_a ≅ B_f` as `B`-algebras for some `f ∉ p` and `a ∉ Q`.
* `Algebra.FinitePresentation.exists_algEquiv_localizationAway_of_algEquiv_atPrime`: algebras
  of finite presentation with isomorphic local rings become isomorphic after inverting one
  element on each side.

## Implementation notes

`R_p` is `Localization.AtPrime p`, `R_f` is `Localization.Away f` and `S_f` is
`Localization.Away (algebraMap R S f)`, an `R_f`-algebra through `Localization.awayMap`; the map
`R_p → S_q` is `Localization.localRingHom p q (algebraMap R S) hpq`.

In `Algebra.FinitePresentation.exists_algEquiv_localizationAway_of_algEquiv_atPrime` the local
rings `Sq` and `Sq'` are any `S`-algebra with `IsLocalization.AtPrime Sq q` whose `R`-algebra
structure is the composite `R → S → Sq` (`IsScalarTower R S Sq`), and similarly for `Sq'`. The
localizations of the conclusion are the models `Localization.Away g` and `Localization.Away g'`;
by uniqueness of localizations (`IsLocalization.algEquiv`) this is no loss of generality. Only
the existence of an `R`-algebra isomorphism `S_g ≅ S'_{g'}` is asserted.

## References

* [Stacks Project, Tag 00QR](https://stacks.math.columbia.edu/tag/00QR)
* [Stacks Project, Tag 00QS](https://stacks.math.columbia.edu/tag/00QS)
-/
