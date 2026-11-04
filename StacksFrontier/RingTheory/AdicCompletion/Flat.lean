module

public import StacksFrontier.RingTheory.AdicCompletion.Flat.DirectSumToPi
public import StacksFrontier.RingTheory.AdicCompletion.Flat.LimitExactness
public import StacksFrontier.RingTheory.AdicCompletion.Flat.TensorLimit
public import StacksFrontier.RingTheory.AdicCompletion.Flat.FlatCompletion

/-!
# Flatness of adic completions

Let `R` be a commutative ring, `I ⊆ R` an ideal, and write `M^∧` for the `I`-adic completion of
an `R`-module `M`. This file proves the following flatness statements about adic completions.

* For `R` Noetherian, completion is exact on finite `R`-modules (injections, surjections and
  middle exactness are preserved), and for a finite module `M` the canonical map
  `R^∧ ⊗_R M → M^∧` is bijective.
* For `R` Noetherian, the ring map `R → R^∧` is flat, and completion carries short exact sequences
  of finite `R`-modules to short exact sequences.
* For `R` Noetherian, if `I` is contained in the Jacobson radical of `R`, then `R → R^∧` is
  faithfully flat; this is stated as the class `Module.FaithfullyFlat R (AdicCompletion I R)`. In
  particular the completion `lim_n R/𝔪ⁿ` of a Noetherian local ring `(R, 𝔪)` is faithfully flat
  over `R`.
* For `R` Noetherian and `I`-adically complete, the canonical map `(⊕_{α ∈ A} R)^∧ → ∏_{α ∈ A} R`
  out of the completion of a direct sum of copies of `R` into the product is universally
  injective.
* For `R` Noetherian, if `(M_n)` is an inverse system of `R`-modules with `M_n` flat over `R/Iⁿ`
  and with surjective transition maps `M_{n+1} → M_n`, then `M = lim M_n` is flat over `R`, and
  for every finite `R`-module `Q` the canonical comparison `Q ⊗_R lim M_n → lim (Q ⊗_R M_n)` is an
  isomorphism.
* For `R` Noetherian the completion `(⊕_{α ∈ A} R)^∧` is a flat `R`-module.
* If `I` is finitely generated, `R/I` is Noetherian, `M/IM` is flat over `R/I` and
  `Tor₁ᴿ(M, R/I) = 0`, then `R^∧` is Noetherian and `M^∧` is flat over `R^∧`. The Tor hypothesis
  is stated after transporting `R`, `M` and `R/I` by `ULift` to the universe `max u v`.

## Main definitions

* `AdicCompletion.directSumToPi`: the canonical map `(⊕_{α ∈ A} R)^∧ → ∏_{α ∈ A} R`.
* `quotientTower`: the tower of quotients `M ⧸ Iⁿ • ⊤` of a module `M`.
* `adicCompletionCone`, `adicCompletionIsLimit`: the `I`-adic completion of `M` as a limit cone
  over `quotientTower I M`.

## Main results

* `adicCompletion_shortExact`: completion carries a short exact sequence with finite middle term
  to a short exact sequence.
* `AdicCompletion.faithfullyFlat_of_le_ringJacobson`: `R^∧` is faithfully flat over a Noetherian
  ring `R` when `I ≤ Ring.jacobson R`.
* `AdicCompletion.universallyInjective_directSumToPi`: the map `directSumToPi` is universally
  injective.
* `flat_limit_and_tensor_limit_of_flat_quotients`: the limit of a surjective tower of modules flat
  over `R ⧸ Iⁿ` is flat, and its tensor product with a finite module commutes with the limit.
* `adicCompletion_flat_of_flat`: the completion of a flat module over a Noetherian ring is flat.
* `AdicCompletion.flat_directSum`: the completion `(⊕_{α ∈ A} R)^∧` is flat.
* `AdicCompletion.isNoetherianRing_and_flat_of_flat_quotient`: under the hypotheses of the last
  item above, `R^∧` is Noetherian and `M^∧` is flat over `R^∧`.

## References

* [Stacks Project, Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Tag 00MC](https://stacks.math.columbia.edu/tag/00MC)
* [Stacks Project, Tag 05BC](https://stacks.math.columbia.edu/tag/05BC)
* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
* [Stacks Project, Tag 06LE](https://stacks.math.columbia.edu/tag/06LE)
* [Stacks Project, Tag 0AGW](https://stacks.math.columbia.edu/tag/0AGW)

## Tags

adic completion, flat, faithfully flat, Jacobson radical, Noetherian ring, inverse limit,
Mittag-Leffler, Tor
-/
