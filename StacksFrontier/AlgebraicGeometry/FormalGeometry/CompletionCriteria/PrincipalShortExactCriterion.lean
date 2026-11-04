module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PrincipalFactorization
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor

/-!
# The short exact sequences of Stacks 0DXW, reduced to one short exactness

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let `(F_n)` be a coherent `I 𝒪_U`-adic
system on `U` and let `f ∈ I`.

`Stacks.Algebraization.HasPrincipalShortExactSequences S F f`, condition (1) of
[Stacks, Tag 0H39] for multiplication by `f`, asks for maps `ι_n : F_n ⟶ F_{n+1}` with
`(F_{n+1} ⟶ F_n) ≫ ι_n = f·` whose sequences `0 → F_n → F_{n+1} → F_1 → 0` are short exact.
Multiplication by `f` on `F_{n+1}` kills `I ⁿ⁺¹ F_{n+1}`, hence factors through the presentation
of `F_n` as `F_{n+1} / I ⁿ⁺¹ F_{n+1}`; this gives canonical maps `ι_n`, and the condition holds as
soon as the resulting sequences are short exact.

## Main definitions

* `Stacks.Algebraization.principalRaise` — the canonical `ι_n : F_n ⟶ F_{n+1}`.
* `Stacks.Algebraization.principalShortComplex` — the sequence
  `0 → F_n → F_{n+1} → F_1 → 0` built from it.

## Main results

* `Stacks.Algebraization.restrictTop_scalarMap_mem_idealOnOpen` — the restriction of `f` to an
  affine open of `U` is a section of `I 𝒪_U` there.
* `Stacks.Algebraization.map_comp_principalRaise` — the factorization identity
  `(F_{n+1} ⟶ F_n) ≫ ι_n = f·`.
* `Stacks.Algebraization.hasPrincipalShortExactSequences_of_shortExact` —
  `Stacks.Algebraization.HasPrincipalShortExactSequences S F f` follows from the short exactness
  of `principalShortComplex`.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (restrictTop)
open Stacks.Cohomology.InverseSystems.TorsionFreeDivisible (Condition1 proj)

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The restriction of a member of `I` to an affine open of `U` is a section of `I 𝒪_U`. -/
theorem restrictTop_scalarMap_mem_idealOnOpen {f : S.A} (hf : f ∈ S.I)
    (V : S.U.toScheme.affineOpens) :
    restrictTop (scalarMap S f) V.1 ∈ (idealOnOpen S).ideal V := by
  simpa only [pow_one] using scalarMap_restrict_mem_idealOnOpen_pow S V 1 (by simpa using hf)

/-- The canonical map `ι_n : F_n ⟶ F_{n+1}`: multiplication by `f` on `F_{n+1}`, read through the
presentation of `F_n` as `F_{n+1} / I ⁿ⁺¹ F_{n+1}`. -/
def principalRaise {f : S.A} (hf : f ∈ S.I) (n : ℕ) :
    systemObj S F n ⟶ systemObj S F (n + 1) :=
  Stacks.Coherent.IsCoherentAdicSystem.principalRaise F.property (scalarMap S f)
    (restrictTop_scalarMap_mem_idealOnOpen S hf) n

/-- Multiplication by `f` on `F_{n+1}` is the transition map followed by `ι_n`. -/
theorem map_comp_principalRaise {f : S.A} (hf : f ∈ S.I) (n : ℕ) :
    systemMapSucc S F n ≫ principalRaise S F hf n =
      (mulBySection S f).app (systemObj S F (n + 1)) :=
  (Stacks.Coherent.IsCoherentAdicSystem.map_comp_principalRaise F.property (scalarMap S f)
      (restrictTop_scalarMap_mem_idealOnOpen S hf) n).trans
    (Stacks.Coherent.mulGlobalSection_app (scalarMap S f) (systemObj S F (n + 1))).symm

/-- The composite `F_n ⟶ F_{n+1} ⟶ F_1` vanishes. -/
theorem principalRaise_comp_proj {f : S.A} (hf : f ∈ S.I) (n : ℕ) :
    principalRaise S F hf n ≫ proj (systemObj S F) (systemMapSucc S F) (n + 1) = 0 :=
  Stacks.Coherent.IsCoherentAdicSystem.principalRaise_comp_eq_zero F.property (scalarMap S f)
    (restrictTop_scalarMap_mem_idealOnOpen S hf) n
    (proj (systemObj S F) (systemMapSucc S F) (n + 1))

/-- The sequence `0 → F_n → F_{n+1} → F_1 → 0` built from `ι_n`, as a short complex. -/
def principalShortComplex {f : S.A} (hf : f ∈ S.I) (n : ℕ) :
    ShortComplex S.U.toScheme.Modules :=
  ShortComplex.mk (principalRaise S F hf n)
    (proj (systemObj S F) (systemMapSucc S F) (n + 1)) (principalRaise_comp_proj S F hf n)

/-- Condition (1) of [Stacks, Tag 0H39] for multiplication by `f` holds as soon as the sequences
`0 → F_n → F_{n+1} → F_1 → 0` built from the canonical maps `ι_n` are short exact. -/
theorem hasPrincipalShortExactSequences_of_shortExact {f : S.A} (hf : f ∈ S.I)
    (hse : ∀ n : ℕ, (principalShortComplex S F hf n).ShortExact) :
    HasPrincipalShortExactSequences S F f :=
  Stacks.Coherent.IsCoherentAdicSystem.condition1_of_shortExact F.property (scalarMap S f)
    (restrictTop_scalarMap_mem_idealOnOpen S hf) hse

end Stacks.Algebraization

end
