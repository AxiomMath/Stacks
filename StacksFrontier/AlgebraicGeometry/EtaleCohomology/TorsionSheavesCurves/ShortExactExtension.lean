module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing

/-!
# The assertions for torsion sheaves on curves pass to extensions

Let `k` be an algebraically closed field, let `X` be a separated scheme of finite type over `k`
whose underlying space has dimension at most one, and let `0 → F₁ → F → F₂ → 0` be a short exact
sequence of torsion abelian sheaves on the small étale site of `X`. Stacks Project Tag 0A5C
asserts that each of the eight statements of Situation 0A52 holds for the middle sheaf `F` as
soon as it holds for the sub- and the quotient sheaf. The eight statements are the vanishing of
`H^q(X, F)` above degree two, its vanishing above degree one when `X` is affine and when `F` is
torsion of characteristic-primary exponent, the finiteness of `H^q(X, F)` for constructible `F`
of torsion prime to the characteristic and for constructible `F` on a proper `X`, the bijectivity
of the restriction map `H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` along an extension `k'/k` of
algebraically closed fields in the same two cases, and the surjectivity of
`H²(X, F) → H²(U, F|_U)` for an open `U ⊆ X`.

Each of the eight is stated as the implication "the statement for the two outer terms of a short
exact sequence gives the statement for the middle term", for an arbitrary scheme, without the base
field, separatedness, finite type or dimension hypotheses of Situation 0A52.

## Main results

* `subsingleton_etaleCohomology_X₂_of_shortExact`: statement (1), the vanishing of étale
  cohomology above degree two.
* `subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine`: statement (2), the vanishing above
  degree one on an affine scheme.
* `subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion`: statement (3), the
  vanishing above degree one for coefficients of characteristic-primary torsion.
* `finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion`: statement (4), the
  finiteness of étale cohomology for constructible coefficients of torsion prime to the
  characteristic.
* `finite_etaleCohomology_X₂_of_shortExact_of_isProper`: statement (5), the finiteness of étale
  cohomology for constructible coefficients over a proper scheme.
* `bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion`:
  statement (6), the bijectivity of restriction for coefficients of torsion prime to the
  characteristic.
* `bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isProper`: statement (7), the
  bijectivity of restriction over a proper scheme.
* `surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing`: statement (8), the
  surjectivity of restriction to an open subscheme in degree two.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section Vanishing

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- If the étale cohomology of the sub- and the quotient sheaf of a short exact sequence of abelian
sheaves vanishes above degree two, then so does that of the middle sheaf. -/
@[stacks 0A5C "vanishing"]
theorem subsingleton_etaleCohomology_X₂_of_shortExact (hS : S.ShortExact)
    (h₁ : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} S.X₁ q))
    (h₃ : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} S.X₂ q) := by
  have := h₁ q hq
  have := h₃ q hq
  exact subsingleton_sheafCohomology_X₂_of_shortExact hS q

/-- If, for an affine scheme, the étale cohomology of the sub- and the quotient sheaf of a short
exact sequence of abelian sheaves vanishes above degree one, then so does that of the middle
sheaf. -/
@[stacks 0A5C "affine vanishing"]
theorem subsingleton_etaleCohomology_X₂_of_shortExact_of_isAffine (hS : S.ShortExact)
    (h₁ : IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₁ q))
    (h₃ : IsAffine X → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (hX : IsAffine X) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w} S.X₂ q) := by
  have := h₁ hX q hq
  have := h₃ hX q hq
  exact subsingleton_sheafCohomology_X₂_of_shortExact hS q

/-- Let `l` be a natural number. If the vanishing of étale cohomology above degree one for
`l`-power torsion coefficients holds for the sub- and the quotient sheaf of a short exact sequence
of abelian sheaves, then it holds for the middle sheaf. -/
@[stacks 0A5C "characteristic-primary vanishing"]
theorem subsingleton_etaleCohomology_X₂_of_shortExact_of_isPrimePowerTorsion
    (l : ℕ) (hS : S.ShortExact)
    (h₁ : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₁ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₁ q))
    (h₃ : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₃ →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l S.X₂) (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H.{w} S.X₂ q) :=
  subsingleton_etaleCohomology_of_shortExact_of_isPrimePowerTorsion'.{w, v, u} l hS h₁ h₃ h₂ q hq

end Vanishing

section Finiteness

variable {X : Scheme.{u}}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
  {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}

/-- Let `p` be a natural number and let `constructible` be a condition on abelian sheaves that
passes from the middle term of the short exact sequence to its sub- and quotient sheaf. If the
finiteness of étale cohomology for coefficients that are constructible and torsion prime to `p`
holds for the sub- and the quotient sheaf of a short exact sequence of abelian sheaves, then it
holds for the middle sheaf. -/
theorem finite_etaleCohomology_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion
    (p : ℕ) (hS : S.ShortExact)
    (hsub : constructible S.X₂ → constructible S.X₁)
    (hquot : constructible S.X₂ → constructible S.X₃)
    (h₁ : constructible S.X₁ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₁ →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₁ q))
    (h₃ : constructible S.X₃ →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₃ →
      ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ q))
    (hc : constructible S.X₂)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₂) (q : ℕ) :
    Finite (Sheaf.H.{w} S.X₂ q) := by
  obtain ⟨hl, hr⟩ := isPrimeToCharacteristicTorsion_of_shortExact p hS ht
  have := h₁ (hsub hc) hl q
  have := h₃ (hquot hc) hr q
  exact finite_sheafCohomology_X₂_of_shortExact hS q

/-- Let `π` be a morphism from `X` to the spectrum of a field `k` and let `constructible` be a
condition on abelian sheaves that passes from the middle term of the short exact sequence to its
sub- and quotient sheaf. If the finiteness of étale cohomology for constructible coefficients
when `π` is proper holds for the sub- and the quotient sheaf of a short exact sequence of abelian
sheaves, then it holds for the middle sheaf. -/
theorem finite_etaleCohomology_X₂_of_shortExact_of_isProper
    {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (hS : S.ShortExact)
    (hsub : constructible S.X₂ → constructible S.X₁)
    (hquot : constructible S.X₂ → constructible S.X₃)
    (h₁ : constructible S.X₁ → IsProper π → ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₁ q))
    (h₃ : constructible S.X₃ → IsProper π → ∀ q : ℕ, Finite (Sheaf.H.{w} S.X₃ q))
    (hc : constructible S.X₂) (hπ : IsProper π) (q : ℕ) :
    Finite (Sheaf.H.{w} S.X₂ q) := by
  have := h₁ (hsub hc) hπ q
  have := h₃ (hquot hc) hπ q
  exact finite_sheafCohomology_X₂_of_shortExact hS q

end Finiteness

section Restriction

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}

/-- Let `p` be a natural number and let `i` be a morphism of schemes. If the bijectivity of
restriction along `i` for coefficients of torsion prime to `p` holds in every degree for the sub-
and the quotient sheaf of a short exact sequence of abelian sheaves, then it holds for the middle
sheaf. -/
@[stacks 0A5C "prime-to-characteristic base change"]
theorem bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isPrimeToCharacteristicTorsion
    (p : ℕ) (hS : S.ShortExact)
    (h₁ : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₁ →
      ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q))
    (h₃ : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₃ →
      ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q))
    (h₂ : Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p S.X₂) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q) := by
  obtain ⟨hl, hr⟩ := isPrimeToCharacteristicTorsion_of_shortExact p hS h₂
  exact etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} i hS (h₁ hl) (h₃ hr) q

/-- Let `π` be a morphism from `X` to the spectrum of a field `k` and let `i` be a morphism of
schemes. If the bijectivity of restriction along `i` when `π` is proper holds in every degree for
the sub- and the quotient sheaf of a short exact sequence of abelian sheaves, then it holds for
the middle sheaf. -/
@[stacks 0A5C "proper base change"]
theorem bijective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_isProper
    {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (hS : S.ShortExact)
    (h₁ : IsProper π → ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q))
    (h₃ : IsProper π → ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q))
    (hπ : IsProper π) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q) :=
  etaleCohomologyRestrictionMap_bijective_of_shortExact.{u, v, w} i hS (h₁ hπ) (h₃ hπ) q

/-- Let `i` be a morphism of schemes. If restriction along `i` is surjective in degree two for the
sub- and the quotient sheaf of a short exact sequence of abelian sheaves, and the étale
cohomology of the sub-sheaf vanishes above degree two, then restriction is surjective in degree
two for the middle sheaf. -/
@[stacks 0A5C "restriction surjectivity"]
theorem surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_vanishing (hS : S.ShortExact)
    (hvanishing : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} S.X₁ q))
    (h₁ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ 2))
    (h₃ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ 2)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ 2) :=
  surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact.{u, v, w} i hS 2 3 rfl
    (hvanishing 3 (by lia)) h₁ h₃

end Restriction

end Stacks.EtaleCohomology

end
