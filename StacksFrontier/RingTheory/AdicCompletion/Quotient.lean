module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Adic completeness descends from a complete quotient

Let `A` be a Noetherian ring, let `I`, `J` be ideals of `A`, assume `A` is `I`-adically complete
and that `A ⧸ I` is `J`-adically complete. Then `A` is `J`-adically complete.

## Main results

* `Stacks.AdicCompletion.QuotientDescent.solution`: the statement of `IsAdicComplete.of_quotient`.

## Implementation notes

Write `B` for the `J`-adic completion of `A`. The source argues through the `(I + J)`-adic
completion `B'` of `A` instead: it identifies `B' ⧸ I B'` with `A ⧸ I`, deduces that `B'` is a
finite `A`-module and that `A → B'` is surjective by Nakayama, gets injectivity from faithful
flatness, and descends `(I + J)`-adic completeness to `J`. The proof below takes the same route
with two contractions, both of which shorten it substantially.

* It uses `B` directly. The two detours the source needs for `I + J` — descending completeness
  from `I + J` to `J` (Stacks 090T) and identifying `B' ⧸ I B'` — collapse into the single
  identification `B ⧸ I B ≅ A ⧸ I`, whose surjectivity half is `surjective_mkQ_comp_of`:
  exactness of `J`-adic completion on `0 → I → A → A ⧸ I → 0` (`AdicCompletion.map_exact`,
  Stacks 00MB (2)) together with `J`-adic precompleteness of `A ⧸ I`. Its one nontrivial input is
  `map_subtype_mem_smul_top`, that for a finitely generated `I` the completion of `I` maps into
  `I • B`: after a surjection from a finite free module the inclusion `I → A` becomes
  `∑ sᵢ • projᵢ` with `sᵢ ∈ I`, and `J`-adic completion is linear in the map.
* Surjectivity of `A → B` is Mathlib's `surjective_of_mkQ_comp_surjective`, the form of Nakayama
  for a complete base and a separated target: it needs `IsPrecomplete I A` and `IsHausdorff I B`
  and *no* finiteness of `B`. So the source's route through finiteness of `B` as an `A`-module
  (Stacks 031D) and through faithful flatness of `A → B` (Stacks 00MB (1), 00HQ) is not needed.
  Here `A → B` is `AdicCompletion.of J A`, and once it is surjective
  `AdicCompletion.of_surjective_iff` gives `IsPrecomplete J A`, which together with
  `IsHausdorff J A` is `J`-adic completeness.

Both separatedness inputs come from the Noetherian Krull intersection theorem
`IsHausdorff.of_le_jacobson`: for `A` itself it applies directly, and for `B` — which is not a
finite `A`-module — through `isHausdorff_adicCompletion`, as each `A ⧸ Jⁿ` is a finite module and
an element of `⋂ₖ Iᵏ B` has all its components in `⋂ₖ Iᵏ (A ⧸ Jⁿ) = 0`. The containment
`I ≤ jacobson ⊥` is Stacks 05GI in the form `IsAdicComplete.le_jacobson_bot`, and
`J ≤ jacobson ⊥` is `le_jacobson_bot_of_map_le`: the image of `J` in `A ⧸ I` lies in
`jacobson ⊥` for the same reason, and a unit modulo an ideal inside `jacobson ⊥` is a unit.

## References

* [StackProject 0DYC](https://stacks.math.columbia.edu/tag/0DYC)
-/

namespace Stacks.AdicCompletion.QuotientDescent

open Submodule _root_.AdicCompletion

section

variable {A : Type*} [CommRing A]

/-- If `I ≤ jacobson ⊥` and the image of `J` in `A ⧸ I` lies in `jacobson ⊥`, then
`J ≤ jacobson ⊥`: an element of `1 + J` is a unit modulo `I`, hence a unit. -/
private theorem le_jacobson_bot_of_map_le (I J : Ideal A) (hI : I ≤ (⊥ : Ideal A).jacobson)
    (hJ : J.map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (A ⧸ I)).jacobson) :
    J ≤ (⊥ : Ideal A).jacobson := by
  have := isLocalHom_of_le_jacobson_bot I hI
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  refine isUnit_of_map_unit (Ideal.Quotient.mk I) _ ?_
  simpa using Ideal.mem_jacobson_bot.mp (hJ (Ideal.mem_map_of_mem _ hx)) (Ideal.Quotient.mk I y)

/-- Over a Noetherian ring, the `J`-adic completion of a finite module `M` is `I`-adically
separated as soon as `I ≤ jacobson ⊥`, even though it is not itself a finite module: every
component of an element of `⋂ₖ Iᵏ • Mˆ` lies in `⋂ₖ Iᵏ • (M ⧸ JⁿM) = 0`. -/
private theorem isHausdorff_adicCompletion [IsNoetherianRing A] (I J : Ideal A) (M : Type*)
    [AddCommGroup M] [Module A M] [Module.Finite A M] (hI : I ≤ (⊥ : Ideal A).jacobson) :
    IsHausdorff I (AdicCompletion J M) := by
  refine ⟨fun x hx => AdicCompletion.ext fun n => ?_⟩
  rw [AdicCompletion.val_zero_apply, ← AdicCompletion.eval_apply]
  refine (IsHausdorff.of_le_jacobson I _ hI).haus _ fun k => SModEq.zero.mpr ?_
  have hmap : (I ^ k • ⊤ : Submodule A (AdicCompletion J M)).map (eval J M n) ≤ I ^ k • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right _ le_top
  exact hmap (Submodule.mem_map_of_mem (SModEq.zero.mp (hx k)))

/-- For a finitely generated ideal `I`, the `J`-adic completion of `I` maps into `I • Aˆ`: a
surjection `Aʳ → I` turns the inclusion `I → A` into `∑ sᵢ • projᵢ` with `sᵢ ∈ I`, and `J`-adic
completion is linear in the map. -/
public theorem map_subtype_mem_smul_top (I J : Ideal A) (hI : I.FG)
    (z : AdicCompletion J (I : Submodule A A)) :
    AdicCompletion.map J (Submodule.subtype (I : Submodule A A)) z
      ∈ I • (⊤ : Submodule A (AdicCompletion J A)) := by
  have : Module.Finite A (I : Submodule A A) := Module.Finite.iff_fg.mpr hI
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := (I : Submodule A A))
  have hψ : Function.Surjective (Fintype.linearCombination A s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  have hcomp : Submodule.subtype (I : Submodule A A) ∘ₗ Fintype.linearCombination A s
      = ∑ i, (s i : A) • (LinearMap.proj i : (Fin r → A) →ₗ[A] A) := by
    ext c
    simp [Fintype.linearCombination, Pi.single_apply]
  obtain ⟨w, rfl⟩ := AdicCompletion.map_surjective J hψ z
  rw [AdicCompletion.map_comp_apply, hcomp, _root_.map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (s i).2 Submodule.mem_top

/-- The identification `Aˆ ⧸ I Aˆ ≅ A ⧸ I` of the source, in the surjective form Nakayama
consumes: over a Noetherian ring, if `A ⧸ I` is `J`-adically precomplete then `A` maps onto
`Aˆ ⧸ I Aˆ`, where `Aˆ` is the `J`-adic completion of `A`.

Given `b : Aˆ`, precompleteness of `A ⧸ I` produces `a : A` with the same image in `(A ⧸ I)ˆ`;
then `b - a` is killed by the completion of `A → A ⧸ I`, so by exactness of `J`-adic completion
on `0 → I → A → A ⧸ I → 0` it comes from the completion of `I`, which lands in `I • Aˆ`. -/
private theorem surjective_mkQ_comp_of [IsNoetherianRing A] (I J : Ideal A)
    [IsPrecomplete J (A ⧸ I)] :
    Function.Surjective
      ((I • (⊤ : Submodule A (AdicCompletion J A))).mkQ ∘ₗ AdicCompletion.of J A) := by
  intro y
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, hc⟩ := AdicCompletion.of_surjective J (A ⧸ I)
    (AdicCompletion.map J (mkQ (I : Submodule A A)) b)
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (I : Submodule A A) c
  refine ⟨a, (Submodule.Quotient.eq _).mpr ?_⟩
  have hker : AdicCompletion.map J (mkQ (I : Submodule A A))
      (b - AdicCompletion.of J A a) = 0 := by
    rw [map_sub, AdicCompletion.map_of, ← hc, sub_self]
  obtain ⟨z, hz⟩ := (AdicCompletion.map_exact (I := J) (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) _).mp hker
  rw [← neg_sub b, ← hz]
  exact neg_mem (map_subtype_mem_smul_top I J (IsNoetherian.noetherian I) z)

end

/-- Over a Noetherian ring `A` that is `I`-adically complete, `J`-adic completeness of `A ⧸ I`
implies `J`-adic completeness of `A`: `A` is `J`-adically Hausdorff by Krull's intersection
theorem, and the map from `A` to its `J`-adic completion is surjective by Nakayama's lemma
applied to `surjective_mkQ_comp_of`. -/
public theorem solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A] (hJ : IsAdicComplete J (A ⧸ I)) :
    IsAdicComplete J A := by
  have hIjac : I ≤ (⊥ : Ideal A).jacobson := IsAdicComplete.le_jacobson_bot I
  have hJjac : J ≤ (⊥ : Ideal A).jacobson :=
    le_jacobson_bot_of_map_le I J hIjac (by
      have : IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I) := by
        rw [← Ideal.Quotient.algebraMap_eq]
        exact (IsAdicComplete.map_algebraMap_iff _ _).mpr hJ
      exact IsAdicComplete.le_jacobson_bot _)
  have : IsPrecomplete J (A ⧸ I) := hJ.toIsPrecomplete
  have : IsHausdorff J A := .of_le_jacobson J A hJjac
  have : IsHausdorff I (AdicCompletion J A) := isHausdorff_adicCompletion I J A hIjac
  have : IsPrecomplete J A :=
    AdicCompletion.of_surjective_iff.mp
      (surjective_of_mkQ_comp_surjective (I := I) (surjective_mkQ_comp_of I J))
  constructor

end Stacks.AdicCompletion.QuotientDescent

/-!
# Adic completeness descends from a complete quotient

Let `A` be a Noetherian ring and let `I`, `J` be ideals of `A`. If `A` is `I`-adically complete
and the quotient `A/I` is `J`-adically complete, then `A` is itself `J`-adically complete.

The mechanism is that the `(I + J)`-adic completion `B` of `A` is already equal to `A`. Indeed
`B/IB` is the `J`-adic completion of `A/I`, hence `A/I` by hypothesis, and `B` is `I`-adically
complete, so `B` is a finite `A`-module; since `I` lies in the Jacobson radical of the
`I`-adically complete ring `A`, Nakayama's lemma makes `A → B` surjective, while `A → B` is flat
with `V(I)` in the image of `Spec(B) → Spec(A)`, hence faithfully flat, hence injective. So `A` is
`(I + J)`-adically complete, and `J`-adic completeness follows because `J ≤ I + J` is finitely
generated.

Thus a Noetherian ring that is complete along `I` inherits from its reduction `A/I` every adic
completeness the reduction has: for instance `ℤ_p[[t]]` is `p`-adically complete because
`ℤ_p[[t]]/(t) = ℤ_p` is.

## Main results

* `IsAdicComplete.of_quotient`: over a Noetherian ring `A` that is `I`-adically complete,
  `J`-adic completeness of `A/I` implies `J`-adic completeness of `A`.

## Implementation notes

The hypothesis "`A/I` is `J`-adically complete" is written `IsAdicComplete J (A ⧸ I)`, along the
ideal `J` of the base ring `A`, rather than along the ideal `J·(A/I)` of the ring `A/I`. The two
say the same thing: the filtrations `Jⁿ • (A ⧸ I)` and `(J·(A/I))ⁿ` are the same submodules of
`A/I`, and `IsAdicComplete.map_algebraMap_iff` turns the literal reading
`IsAdicComplete (J.map (Ideal.Quotient.mk I)) (A ⧸ I)` into the one used here by a single
rewrite. The form over the base ring is Mathlib's normal form (it is the right-hand side of that
iff) and lets the same `J` serve both the hypothesis and the conclusion, with no `Ideal.map`.

`IsAdicComplete I A` is an instance argument, the shape it carries in
`IsAdicComplete.le_jacobson_bot`; the completeness of the quotient is an explicit hypothesis,
since instance search has no way to discover it.

The source's proof first obtains `(I + J)`-adic completeness of `A` and then descends to `J`
using that `M` complete along an ideal is complete along any finitely generated smaller ideal
(Lemma 090T, `isAdicComplete_of_le_of_fg_of_isAdicComplete`), which applies as every ideal of a
Noetherian ring is finitely generated. The conclusion stated here is the source's, `J`-adic
completeness; the `(I + J)`-adic statement is a step of that proof rather than this lemma.

Remarks on the statement.

* Every hypothesis is used by the conclusion: `IsAdicComplete J (A ⧸ I)` is what makes the
  conclusion informative (for `I = ⊥` it is the conclusion, transported along `A ⧸ ⊥ ≃ A`), and
  `IsAdicComplete I A` cannot be dropped: take `A = ℤ` and `I = J = (3)`. Then the filtration
  `(3)ⁿ • (ℤ ⧸ (3))` is `⊥` for every `n ≥ 1`, so `ℤ ⧸ (3)` is `(3)`-adically complete, while
  `ℤ` itself is not, since `IsAdicComplete (3) ℤ` would force `(3) ≤ jacobson ⊥` and `3 * 1 + 1 = 4`
  is not a unit of `ℤ`. Taking instead `J` invertible on `A ⧸ I` does *not* witness this: for
  `I = (2)`, `J = (3)` the filtration `(3)ⁿ • (ℤ ⧸ (2))` is `⊤` at every `n`, so `ℤ ⧸ (2)` is not
  `(3)`-adically complete either. Finally `IsNoetherianRing A` carries both the flatness of
  `A → B` and the finiteness of `B` as an `A`-module.
* The scalars and the base are the source's: `I` and `J` are ideals of `A` itself, the completeness
  of `A/I` is along that same `J`, and the module structure on `A ⧸ I` is restriction of scalars
  along `A → A/I`; no localization and no change of base ring intervenes.
* No canonical map has to be pinned separately: `IsAdicComplete J A` says exactly that the
  canonical map `A → lim_n A/JⁿA` is bijective, injectivity being `IsHausdorff` and surjectivity
  `IsPrecomplete`, so the map the source calls completion is pinned by the class itself.
* The instantiation is not degenerate: take `A = ℤ_p[[t]]`, which is Noetherian and `(t)`-adically
  complete, `I = (t)` and `J = (p)`. Then `A/I = ℤ_p` is `p`-adically complete, and the conclusion
  says `ℤ_p[[t]]` is `p`-adically complete, its `p`-adic completion being `lim_n (ℤ/pⁿ)[[t]]`.
  Here `J ≰ I`, which rules out the degenerate case in which `J` dies in `A/I` and the conclusion
  already follows from `IsAdicComplete I A` alone, and neither ideal is `⊥` or `⊤`.

## References

* [StackProject 0DYC](https://stacks.math.columbia.edu/tag/0DYC)

## Tags

adic completeness, Noetherian ring, quotient ring
-/

@[expose] public section

/-- Let `A` be a Noetherian ring and let `I`, `J` be ideals of `A`. If `A` is `I`-adically
complete and `A/I` is `J`-adically complete, then `A` is `J`-adically complete. -/
@[stacks 0DYC "The hypothesis on `A/I` is stated along the ideal `J` of the base ring `A`,
Mathlib's normal form via `IsAdicComplete.map_algebraMap_iff`. See the module docstring."]
public theorem IsAdicComplete.of_quotient {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A] (hJ : IsAdicComplete J (A ⧸ I)) :
    IsAdicComplete J A :=
  Stacks.AdicCompletion.QuotientDescent.solution I J hJ

end
