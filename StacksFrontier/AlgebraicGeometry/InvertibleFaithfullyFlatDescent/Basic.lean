module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Basic
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithfully flat descent of invertibility of a module

Let `R → S` be a faithfully flat ring map and `M` an `R`-module.  This file proves that `M` is
an invertible `R`-module as soon as `S ⊗[R] M` is an invertible `S`-module, in the concrete
`S ⊗[R] M` form and in the `IsBaseChange` form a geometric consumer has.

This is the invertibility analogue of Stacks Proposition 058S, the statement that finite
projectivity descends along a faithfully flat ring map.  058S itself is available —
`Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat`, with the finiteness half
Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` — and *invertibility* does
not follow from it, because an invertible module is finite projective **of rank one**, and no
faithfully flat descent of `Module.rankAtStalk` exists in Mathlib or in either tree.  Supplying
that missing third ingredient is the content here, and it is where faithful flatness is used a
second time.

## Main results

* `Module.Invertible.of_invertible_tensorProduct`: if `S` is a faithfully flat `R`-algebra and
  `S ⊗[R] M` is an invertible `S`-module, then `M` is an invertible `R`-module.
The shape in which the hypothesis usually arrives — an arbitrary `R`-linear map
`f : M →ₗ[R] N` exhibiting an `S`-module `N` as the base change of `M` — is
`Module.Invertible.of_isBaseChange_of_faithfullyFlat`, which is proved for `R` and `S` in
independent universes and is imported here rather than restated.

## The route

Invertibility is equivalent to being finite projective of constant rank one at every prime, by
`Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse` (Stacks Tag
0B8I), and each of the three conditions descends separately:

* finiteness is Mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`;
* projectivity is this repository's `Module.Projective.of_projective_tensorProduct`
  (Stacks Tag 05A9), which needs no finiteness;
* the rank condition is the step with no ready-made descent lemma.  It is obtained from
  Mathlib's `Module.rankAtStalk_baseChange`, which computes the rank of a base change at a prime
  of `S` as the rank of `M` at the prime it contracts to, together with surjectivity of
  `PrimeSpectrum.comap (algebraMap R S)` for a faithfully flat algebra
  (`PrimeSpectrum.comap_surjective_of_faithfullyFlat`).  Every prime of `R` is therefore hit,
  and at each of them the rank is read off from the rank of `S ⊗[R] M`, which is identically one
  because that module is invertible.

So faithful flatness is used twice and for different reasons: once to descend projectivity, and
once to know that no prime of `R` is missed by `Spec S → Spec R`.  Flatness alone does not
suffice for either, and the counterexample recorded for projectivity — `ℤ → ℚ` with `M = ℚ` —
also defeats the rank step, since `Spec ℚ → Spec ℤ` misses every nonzero prime.

`Module.rankAtStalk_baseChange` carries `[Module.Flat R M]` and `[Module.Finite R M]` as ambient
hypotheses, so the two preceding steps have to be performed first and in that order; projectivity
supplies flatness by instance.

## What is not done

**Nothing here is about schemes, and no `@[stacks]` attribute is attached.**  Proposition 058S's
own statement is about finite projectivity and is tagged where it is proved; this is a different
statement, and the Stacks project has no separate tag for it.

The converse direction — invertibility of `M` giving invertibility of `S ⊗[R] M` — is Mathlib's
`Module.Invertible.instTensorProduct` and needs no flatness; it is not restated.

This is one of the two inputs the proof of Stacks Tag 0CDX takes, the other being degree-zero
flat base change for the global sections of a **quasi-coherent module** on a quasi-compact
quasi-separated scheme, i.e. Tag 02KH part (2) at `i = 0`.  That second input is absent from
Mathlib and from both trees at the present pin — what exists, as
`Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.isPushout_appTop`, is the case of the
structure sheaf — and nothing in this file addresses it.

A consumer that has the multiplication pairing `M ⊗[R] N →ₗ[R] R` in hand does not need this
file at all: bijectivity of such a pairing gives invertibility of both factors directly, by
Mathlib's `Module.Invertible.left` and `Module.Invertible.right`, and bijectivity itself
descends by `Module.FaithfullyFlat.lTensor_bijective_iff_bijective`.  The theorems here are for
a consumer who knows only that the base change is invertible.

## References

* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
* [Stacks Project, Tag 05A9](https://stacks.math.columbia.edu/tag/05A9)
* [Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace Module

/-- **Faithfully flat descent of invertibility.**  If `S` is a faithfully flat `R`-algebra and
the `S`-module `S ⊗[R] M` is invertible, then `M` is an invertible `R`-module.

This is the invertibility analogue of Stacks Proposition 058S.  Finiteness and projectivity
descend by 058S and Tag 05A9; the remaining ingredient, constancy of the rank at value one, is
obtained from `Module.rankAtStalk_baseChange` and surjectivity of `Spec S → Spec R`. -/
@[sga "1 VIII 1.11" "special case", sga "4½ Arcata 1.4.2"]
public theorem Invertible.of_invertible_tensorProduct {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (S : Type u) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.Invertible S (S ⊗[R] M)] :
    Module.Invertible R M := by
  have hfin : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have hproj : Module.Projective R M := Module.Projective.of_projective_tensorProduct S
  have hflat : Module.Flat R M := Module.Flat.of_projective
  have hup := (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u,
    max v u, 0} S (S ⊗[R] M)).1.out 2 1
  have hone : Module.rankAtStalk (R := S) (S ⊗[R] M) =
      Function.const (PrimeSpectrum S) 1 := (hup.mp inferInstance).2.2
  have hrank : Module.rankAtStalk (R := R) M = Function.const (PrimeSpectrum R) 1 := by
    funext p
    obtain ⟨q, hq⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) p
    have h := Module.rankAtStalk_baseChange (R := R) (M := M) (S := S) q
    rw [hq] at h
    rw [← h, hone]
    rfl
  have hdown := (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u,
    v, 0} R M).1.out 1 2
  exact hdown.mp ⟨hfin, hproj, hrank⟩

end Module

end
