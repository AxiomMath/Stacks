module

import StacksFrontier.RingTheory.Depth.Dimension
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat

public import StacksFrontier.RingTheory.Sequence.BaseChange
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.Nakayama
import StacksFrontier.RingTheory.KrullDimension.QuotientHeight

@[expose] public section

/-!
# Cohen–Macaulayness ascends along a flat local homomorphism of small enough dimension

Proof of `Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat` (Stacks 00R5): if
`R → S` is a flat local homomorphism of Noetherian local rings with `R` Cohen–Macaulay, and `S`
is either finite over `R` or of dimension at most `dim(R)`, then `S` is Cohen–Macaulay and
`dim(R) = dim(S)`.

The proof is a chain of four comparisons closing on itself:
`dim(R) = depth_{𝔪_R}(R) ≤ depth_{𝔪_S}(S) ≤ dim(S) ≤ dim(R)`. The first equality is the
Cohen–Macaulayness of `R`. The middle inequality is the content: a flat local homomorphism of
local rings is faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`) and `S` is the base
change of `R` along itself (`IsBaseChange.linearMap`), so an `R`-regular sequence in `𝔪_R` has
`S`-regular image (Stacks 00LM), and that image lies in `𝔪_S` because the homomorphism is local;
comparing the two suprema defining the depths gives the inequality. The third is
`depth_I(M) ≤ dim(Supp(M))` (Stacks 00LK) for `M = S`, whose support is all of `Spec(S)`. The last
is the hypothesis in the second case, and in the finite case it is an equality already: a finite
faithfully flat algebra is integral with injective structure map, so `dim(R) = dim(S)` by
Stacks 00OK.

## Implementation notes

The middle inequality is proved in the generality the argument has, as
`depth_le_depth_of_isBaseChange`: `depth_I(M) ≤ depth_J(N)` for `N` a base change of `M` along a
faithfully flat `R → S` and `J` an ideal of `S` containing `I·S`, with no locality involved.
Locality enters only in the specialization `depth_le_depth_of_flat_of_isLocalHom`, where it
supplies both the faithful flatness and the containment `𝔪_R·S ⊆ 𝔪_S`
(`IsLocalRing.map_maximalIdeal_le`); that specialization is the inequality the source states, and
the endgame is the four-term chain and two antisymmetries.

Both depths are read off the definition (Stacks 00LI), whose supremum branch is the relevant one
because `𝔪 • (⊤ : Submodule R R) = 𝔪 ≠ ⊤` for the maximal ideal of a local ring
(`Module.maximalIdeal_smul_top_ne_top`).

## References

* [StackProject 00R5](https://stacks.math.columbia.edu/tag/00R5)
* [StackProject 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [StackProject 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/


namespace Stacks.CohenMacaulay.FlatLocalAscent

open IsLocalRing RingTheory.Sequence

/-- **Depth grows under faithfully flat base change.** Let `S` be a faithfully flat `R`-algebra,
let `f : M →ₗ[R] N` exhibit `N` as the base change of `M` to `S`, and let `J` be an ideal of `S`
containing the image of an ideal `I` of `R`. If `I • M ≠ M` and `J • N ≠ N`, then
`depth_I(M) ≤ depth_J(N)`: an `M`-regular sequence in `I` maps to an `N`-regular sequence in `J`
(Stacks 00LM) of the same length. -/
private theorem depth_le_depth_of_isBaseChange {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {I : Ideal R} {J : Ideal S} (hIJ : I.map (algebraMap R S) ≤ J)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (hJ : J • (⊤ : Submodule S N) ≠ ⊤) :
    Module.depth R I M ≤ Module.depth S J N := by
  rw [Module.depth, Module.depth, ite_eq_right hI, ite_eq_right hJ]
  refine iSup₂_le fun rs hrs => le_iSup₂_of_le (rs.map (algebraMap R S)) ⟨?_, ?_⟩ (by simp)
  · rintro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact hIJ (Ideal.mem_map_of_mem _ (hrs.1 x hx))
  · exact (isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange hf rs).mpr hrs.2

/-- **Depth ascends along a flat local homomorphism.** If `R → S` is a flat local homomorphism of
local rings, then `depth_{𝔪_R}(R) ≤ depth_{𝔪_S}(S)`. Such a homomorphism is faithfully flat, `S`
is the base change of `R` along itself, and `𝔪_R` maps into `𝔪_S`. -/
private theorem depth_le_depth_of_flat_of_isLocalHom (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] :
    Module.depth R (maximalIdeal R) R ≤ Module.depth S (maximalIdeal S) S := by
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := R) (B := S)
  exact depth_le_depth_of_isBaseChange (IsBaseChange.linearMap R S)
    (map_maximalIdeal_le (algebraMap R S)) (Module.maximalIdeal_smul_top_ne_top R)
    (Module.maximalIdeal_smul_top_ne_top S)

/-- If `R → S` is a flat local homomorphism of Noetherian local rings with `R` Cohen–Macaulay,
and `S` is either finite over `R` or satisfies `dim(S) ≤ dim(R)`, then `S` is Cohen–Macaulay and
`dim(R) = dim(S)`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] (hR : Module.IsMaximalCohenMacaulay R R)
    (h : Module.Finite R S ∨ ringKrullDim S ≤ ringKrullDim R) :
    Module.IsMaximalCohenMacaulay S S ∧ ringKrullDim R = ringKrullDim S := by
  have hR' : (Module.depth R (maximalIdeal R) R : WithBot ℕ∞) = ringKrullDim R := hR
  -- `dim(R) = depth_{𝔪_R}(R) ≤ depth_{𝔪_S}(S)`, by Stacks 00LM.
  have hRle : ringKrullDim R ≤ (Module.depth S (maximalIdeal S) S : WithBot ℕ∞) :=
    hR' ▸ WithBot.coe_le_coe.mpr (depth_le_depth_of_flat_of_isLocalHom R S)
  -- `depth_{𝔪_S}(S) ≤ dim(Supp(S)) = dim(S)`, by Stacks 00LK.
  have hSle : (Module.depth S (maximalIdeal S) S : WithBot ℕ∞) ≤ ringKrullDim S :=
    Module.supportDim_self_eq_ringKrullDim S ▸
      Module.depth_le_supportDim S _ S (Module.maximalIdeal_smul_top_ne_top S)
  -- `dim(S) ≤ dim(R)`: assumed in the second case; in the first, `S` is finite and faithfully
  -- flat over `R`, hence integral with injective structure map, so Stacks 00OK gives equality.
  have hdimS : ringKrullDim S ≤ ringKrullDim R := by
    rcases h with hfin | hle
    · have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := R) (B := S)
      have := Algebra.IsIntegral.of_finite R S
      exact (Algebra.IsIntegral.ringKrullDim_eq R S).ge
    · exact hle
  have hdim : ringKrullDim R = ringKrullDim S := le_antisymm (hRle.trans hSle) hdimS
  exact ⟨le_antisymm hSle (hdim ▸ hRle), hdim⟩

end Stacks.CohenMacaulay.FlatLocalAscent

end

/-!
# Cohen–Macaulayness ascends along a flat local homomorphism of small enough dimension

Let `R → S` be a local homomorphism of Noetherian local rings with `R` Cohen–Macaulay. If `S` is
finite flat over `R`, or if `S` is flat over `R` and `dim(S) ≤ dim(R)`, then `S` is Cohen–Macaulay
and `dim(R) = dim(S)`.

The mechanism is depth. Pick an `R`-regular sequence `x₁, …, x_d` in `𝔪_R` of length
`d = dim(R)`, which exists because `R` is Cohen–Macaulay. A flat local homomorphism of local rings
is faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), so the image of that sequence
is `S`-regular (tag 00LM) and lies in `𝔪_S`; hence `depth_{𝔪_S}(S) ≥ d`. On the other hand
`depth_{𝔪_S}(S) ≤ dim(S)` for a nonzero finite module over a Noetherian local ring (tag 00LK).
Combined with `dim(S) ≤ d` this forces `depth_{𝔪_S}(S) = dim(S) = d = dim(R)`, which is both
conclusions at once. In the finite case the inequality `dim(S) ≤ dim(R)` is not an assumption but
a consequence: a finite algebra is integral and a faithfully flat one is injective, so
`dim(R) = dim(S)` already by tag 00OK.

## Main results

* `Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat`: Stacks 00R5.

## Implementation notes

Cohen–Macaulayness of a Noetherian local ring `A` (Definition 00N8: `A` is Cohen–Macaulay as a
module over itself) is spelled `Module.IsMaximalCohenMacaulay A A`, that is
`depth_{𝔪_A}(A) = dim(A)` (tag 00NF), as in the companion statements for tags 00NA and 00NB. For `M = A`
the module notion of Definition 00N3, `dim(Supp(M)) = depth(M)`, agrees with the maximal one
because `Supp(A) = Spec(A)`.

The local homomorphism `R → S` is an `Algebra R S` structure with `IsLocalHom (algebraMap R S)`,
and `S` flat over `R` is `Module.Flat R S`; this is the shape used by tag 00LM, whose statement
this one consumes. Both dimensions are `ringKrullDim`, valued in `WithBot ℕ∞`, so the statement
needs no finiteness of dimension.

The source's two alternatives are kept as the single disjunctive hypothesis
`Module.Finite R S ∨ ringKrullDim S ≤ ringKrullDim R` on top of the flatness shared by both,
rather than split into two theorems, so that one declaration states the whole lemma. The first
disjunct is *not* redundant decoration in the sense of being unused: it is the branch that
downstream applications provide (Lemma 045M applies 00R5 to a finite free ring map, where no
dimension inequality is available beforehand), and deducing the second disjunct from it is exactly
the appeal to tag 00OK that the source's proof makes.

Faithfulness to [StackProject 00R5]:

1. No hypothesis is idle. `hR` is the source's "R Cohen–Macaulay" and without it `S` need not be
   Cohen–Macaulay (`R = k[x, y]_{(x, y)}/(x², xy)` is not, and `S = R` is a finite flat `R`-algebra
   of the same dimension); `Module.Flat R S` and `IsLocalHom (algebraMap R S)` are what carry the
   regular sequence from `R` to `S`; `h` is what bounds `dim(S)`, and it fails for
   `R = k`, `S = k[x]_{(x)}`, a flat non-finite local extension with `dim(S) = 1 > 0 = dim(R)`,
   where the dimension equality of the conclusion breaks; both Noetherian hypotheses are used by
   the depth inequalities above.
2. The scalars and base are the source's. `depth_{𝔪_R}(R)` is taken over `R` along the maximal
   ideal of `R`, `depth_{𝔪_S}(S)` over `S` along the maximal ideal of `S`, and the two dimensions
   are those of `R` and `S` themselves; nothing is a base change or a localisation.
3. The map the source names is pinned. "Local homomorphism `R → S`" is `algebraMap R S` together
   with `IsLocalHom (algebraMap R S)`, and flatness and finiteness refer to that same map; the
   conclusion is an equation between named quantities, not an existence claim.
4. The instantiation is not degenerate. With `R = k[x]_{(x)}` and `S = k[y]_{(y)}` via `x ↦ y²`,
   the map is a finite flat local homomorphism of Noetherian local rings, `R` is Cohen–Macaulay,
   and the conclusion holds with `dim(R) = dim(S) = 1`; the second disjunct is met nonvacuously by
   `R = S = k[x]_{(x)}` with the identity. Neither branch of `h` is vacuous, and the hypotheses do
   not force `R = S`.

## References

* [StackProject 00R5](https://stacks.math.columbia.edu/tag/00R5)
* [StackProject 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [StackProject 00OK](https://stacks.math.columbia.edu/tag/00OK)

## Tags

Cohen-Macaulay ring, flat local homomorphism, depth, Krull dimension
-/


/-- **Stacks 00R5.** Let `R → S` be a local homomorphism of Noetherian local rings with `R`
Cohen–Macaulay, i.e. `depth_{𝔪_R}(R) = dim(R)`. If `S` is flat over `R` and is either finite over
`R` or of dimension at most `dim(R)`, then `S` is Cohen–Macaulay and `dim(R) = dim(S)`. -/
@[stacks 00R5 "Cohen-Macaulayness of a Noetherian local ring `A` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A`, i.e. `depth_{𝔪_A}(A) = dim A`; the source's two alternatives
are the disjunctive hypothesis `h` over the flatness common to both. See the module docstring.",
  ega "0 17.3.5" "(ii) necessity"]
public theorem Module.isMaximalCohenMacaulay_self_and_ringKrullDim_eq_of_flat
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] (hR : Module.IsMaximalCohenMacaulay R R)
    (h : Module.Finite R S ∨ ringKrullDim S ≤ ringKrullDim R) :
    Module.IsMaximalCohenMacaulay S S ∧ ringKrullDim R = ringKrullDim S :=
    by exact Stacks.CohenMacaulay.FlatLocalAscent.solution hR h


/-!
# Cohen–Macaulayness along a flat local homomorphism

Proof of `Module.isMaximalCohenMacaulay_self_iff_of_flat` (Stacks 045J): for a flat local
homomorphism `R → S` of local rings with `S` Noetherian, `S` is Cohen–Macaulay if and only if
`R` and the fibre ring `S/𝔪_R S` are Cohen–Macaulay.

Both invariants are additive along such a homomorphism: depth is, by Stacks 0337,
`depth(S) = depth(R) + depth(S/𝔪_R S)`, and so is dimension, by Stacks 00ON,
`dim(S) = dim(R) + dim(S/𝔪_R S)`. Since `depth ≤ dim` holds for each of the three (Stacks 00LK)
and the two dimensions on the right are finite, the equation `depth(S) = dim(S)` between the two
sums holds exactly when it holds summand by summand: two comparable finite pieces cannot
compensate for one another.

## Main results

* `Stacks.CohenMacaulay.FlatFibreCriterion.solution`: the statement of Stacks 045J.

## Implementation notes

The three dimensions enter as heights of maximal ideals rather than as Krull dimensions, that
being the form dimension additivity takes and the form in which the two summands on the right are
visibly finite. Additivity itself is
`height_maximalIdeal_eq_height_add_height_map_maximalIdeal`, the height formula in a going-down
extension applied to `𝔪_S` over `𝔪_R`; flatness supplies going down and locality of the
homomorphism makes `𝔪_S` lie over `𝔪_R`. The fibre's dimension is the height of the image of
`𝔪_S`, which is the maximal ideal of the local ring `S ⧸ 𝔪_R S`; that is
`ringKrullDim_quotient_eq_height_map_maximalIdeal`.

The hypothesis `𝔪 • M ≠ M` of Stacks 00LK is Nakayama's lemma for a nonzero finite module over a
local ring, so both applications of `depth ≤ dim` — for `R` over itself and for the fibre — are
instances of the single lemma `depth_maximalIdeal_le_of_supportDim_eq`, which differ only in the
identification of `dim Supp` with a height that each supplies.

`IsNoetherianRing R` is not among the hypotheses, and both additivity formulas need it; it is
derived as in Stacks 0337, from `S ⊗[R] R ≃ₗ[S] S` being a Noetherian `S`-module and
Noetherianity descending along the faithfully flat base change `R → S`.

## References

* [StacksProject 045J](https://stacks.math.columbia.edu/tag/045J)
* [StacksProject 0337](https://stacks.math.columbia.edu/tag/0337)
* [StacksProject 00ON](https://stacks.math.columbia.edu/tag/00ON)

## Tags

Cohen-Macaulay local ring, depth, flat local homomorphism, fibre ring, Krull dimension
-/

open IsLocalRing TensorProduct


namespace Stacks.CohenMacaulay.FlatFibreCriterion

/-- **Depth is at most the dimension of the support** (Stacks 00LK) for a nonzero finite module
`M` over a local ring, read in `ℕ∞` against any height `d` computing `dim Supp M`. The
hypothesis `𝔪 • M ≠ M` of Stacks 00LK is Nakayama's lemma here, so it does not appear. -/
private lemma depth_maximalIdeal_le_of_supportDim_eq (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] {d : ℕ∞}
    (hd : Module.supportDim R M = (d : WithBot ℕ∞)) :
    Module.depth R (maximalIdeal R) M ≤ d := by
  have h := Module.depth_le_supportDim R (maximalIdeal R) M
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)).symm
  rw [hd] at h
  exact_mod_cast h

/-- **Dimension is additive along a flat local homomorphism** (Stacks 00ON): for `R → S` a flat
local homomorphism of Noetherian local rings, `dim S = dim R + dim (S ⧸ 𝔪_R S)`. It is stated as
an equation of heights of maximal ideals, which is what the height formula in a going-down
extension gives; `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` and
`ringKrullDim_quotient_eq_height_map_maximalIdeal` turn the three heights into the three
dimensions. Going down is available because `S` is flat over `R`, and `𝔪_S` lies over `𝔪_R`
because the homomorphism is local. -/
@[ega "IV 21.10.1" "partial",
  ega "IV 6.1.1" "Flat case of (6.1.1.1)",
  ega "IV 6.1.2",
  ega "IV 6.1.3" "special case"]
private lemma height_maximalIdeal_eq_height_add_height_map_maximalIdeal (R S : Type*)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    (maximalIdeal S).height = (maximalIdeal R).height
      + ((maximalIdeal S).map
          (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)))).height :=
  have : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown _ _

/-- Two sums in `ℕ∞` of comparable terms with finite right-hand summands are equal exactly when
the summands agree: neither piece can compensate for the other. This is the `WithTop` analogue of
`add_eq_add_iff_eq_and_eq`, which needs a strict monotonicity `ℕ∞` does not have. -/
private lemma add_eq_add_iff_of_le_of_ne_top {a b A B : ℕ∞} (ha : a ≤ A) (hb : b ≤ B)
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) : a + b = A + B ↔ a = A ∧ b = B := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩
  have hbB : b = B := WithTop.add_left_cancel hA
    (le_antisymm (add_le_add le_rfl hb) (h.symm.trans_le (add_le_add ha le_rfl)))
  rw [hbB] at h
  exact ⟨WithTop.add_right_cancel hB h, hbB⟩

/-- For a flat local homomorphism `R → S` of local rings with `S` Noetherian, `S` is
Cohen–Macaulay if and only if `R` is Cohen–Macaulay and the closed fibre `S ⧸ 𝔪_R S` has
`depth_{𝔪_S}(S ⧸ 𝔪_R S) = dim(S ⧸ 𝔪_R S)`. -/
public theorem solution (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    Module.IsMaximalCohenMacaulay S S ↔
      Module.IsMaximalCohenMacaulay R R ∧
        (Module.depth S (IsLocalRing.maximalIdeal S)
              (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) : WithBot ℕ∞) =
          ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  -- `R` is Noetherian because `S ⊗[R] R ≃ₗ[S] S` is and `R → S` is faithfully flat.
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
      (isNoetherian_of_linearEquiv (AlgebraTensorModule.rid R S S).symm)
  set I : Ideal S := (maximalIdeal R).map (algebraMap R S)
  have hItop : I ≠ ⊤ := (map_maximalIdeal_lt_top (algebraMap R S)).ne
  have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing (S ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  unfold Module.IsMaximalCohenMacaulay
  rw [← maximalIdeal_height_eq_ringKrullDim (R := R),
    ← maximalIdeal_height_eq_ringKrullDim (R := S),
    ringKrullDim_quotient_eq_height_map_maximalIdeal hItop,
    Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal R S,
    height_maximalIdeal_eq_height_add_height_map_maximalIdeal R S]
  simp only [WithBot.coe_inj]
  exact add_eq_add_iff_of_le_of_ne_top
    (depth_maximalIdeal_le_of_supportDim_eq R R
      (by rw [Module.supportDim_self_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]))
    (depth_maximalIdeal_le_of_supportDim_eq S (S ⧸ I)
      (by rw [Module.supportDim_quotient_eq_ringKrullDim,
        ringKrullDim_quotient_eq_height_map_maximalIdeal hItop]))
    Ideal.height_ne_top_of_isPrime
    (by rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
        exact Ideal.height_ne_top_of_isPrime)

end Stacks.CohenMacaulay.FlatFibreCriterion


/-!
# Cohen–Macaulayness along a flat local homomorphism

Let `R → S` be a flat local homomorphism of Noetherian local rings, with maximal ideals `𝔪_R`
and `𝔪_S`. Then `S` is Cohen–Macaulay if and only if both `R` and the fibre ring `S/𝔪_R S` are
Cohen–Macaulay.

What makes this work is that the two invariants involved are additive along such a homomorphism.
Depth is additive, `depth(S) = depth(R) + depth(S/𝔪_R S)` (Tag 0337), and so is dimension,
`dim(S) = dim(R) + dim(S/𝔪_R S)` (Tag 00ON, in Mathlib as
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, going down being available because the
map is flat). Since `depth ≤ dim` for every nonzero finite module over a Noetherian local ring
(Tag 00LK, `Module.depth_le_supportDim`), and since all six quantities are finite — the fibre is
a nonzero ring because `𝔪_R S ⊆ 𝔪_S`, the homomorphism being local — two sums of comparable
terms are equal exactly when they are equal summand by summand. So `depth(S) = dim(S)` forces
both `depth(R) = dim(R)` and `depth(S/𝔪_R S) = dim(S/𝔪_R S)`, and conversely.

## Main results

* `Module.isMaximalCohenMacaulay_self_iff_of_flat`: for `R → S` a flat local homomorphism of
  Noetherian local rings, `S` is Cohen–Macaulay if and only if `R` and `S/𝔪_R S` are.

## Implementation notes

Cohen–Macaulayness of a Noetherian local ring `A` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A`, that is `depth_{𝔪_A}(A) = dim(A)`, following the companion
statements of Tags 00R5, 00RE, 00RF and 00RG. This is how it is said of `S` and of `R`.

For the fibre the same equation is written out, as `depth_{𝔪_S}(S/𝔪_R S) = dim(S/𝔪_R S)`, with
the depth taken over `S` along `𝔪_S` rather than over the local ring `S/𝔪_R S` along its own
maximal ideal. The two depths agree: `𝔪_S` surjects onto the maximal ideal `𝔪_S/𝔪_R S` of
`S/𝔪_R S`, and an element of `𝔪_S` acts on `S/𝔪_R S` and on its further quotients as its image
does, so the `S`-regular sequences in `𝔪_S` and the `(S/𝔪_R S)`-regular sequences in
`𝔪_S/𝔪_R S` correspond length by length. This is the spelling of the fibre depth in Tag 0337 and
in Mathlib's `IsLocalRing.length_baseChange`, and it is what lets the statement do without an
`IsLocalRing (S ⧸ 𝔪_R S)` instance, of which there is none: a quotient of a local ring is local
only for a proper ideal, and `𝔪_R S ≠ ⊤` is a consequence of the hypotheses rather than
something instance resolution can see. The dimension of the fibre is `ringKrullDim (S ⧸ 𝔪_R S)`,
its dimension as a ring, which by `Module.supportDim_quotient_eq_ringKrullDim` is also
`dim Supp(S/𝔪_R S)` computed over `S`; so the conjunct is at once Definition 00N8 for the local
ring `S/𝔪_R S` and Definition 00N3 for the `S`-module `S/𝔪_R S`.

Faithfulness to [StacksProject 045J]:

1. No dead hypothesis. Flatness is used: for `R = k[x, y]_{(x, y)}` and `S = R/(x^2, xy)` the
   map is a local homomorphism of Noetherian local rings, the fibre `S/𝔪_R S` is the field `k`
   and `R` is regular, so the right-hand side holds, while `S` is not Cohen–Macaulay — the class
   of `x` is a nonzero element of `S` killed by `𝔪_S`, so `depth(S) = 0`, whereas `dim(S) = 1`
   because `(x^2, xy) = x · (x, y)` has `(x)` as its only minimal prime. Locality of the
   homomorphism is used: for `R = k[x]_{(x)}` and `S = k(x)`, flat because it is a localisation,
   the fibre is the zero ring, whose depth is `⊤` and whose dimension is `⊥`, so the right-hand
   side fails, while `S`, a field, is Cohen–Macaulay. `IsNoetherianRing S` is used by both
   additivity formulas and by `depth ≤ dim`. Locality of `R` and of `S` is what makes `depth_𝔪`
   and `ringKrullDim` the depth and the dimension of the source and of the target.
2. The scalars and base are the source's. `depth(S)` and `dim(S)` are formed over `S`,
   `depth(R)` and `dim(R)` over `R`, and the fibre's depth over `S` along `𝔪_S`, which is its
   depth as a local ring in its own right by the paragraph above; no localisation or base change
   other than the fibre itself intervenes.
3. The homomorphism is pinned, not merely assumed to exist: `Algebra R S` provides it as
   `algebraMap R S`, `IsLocalHom (algebraMap R S)` says that this map is local,
   `Module.Flat R S` says that `S` is flat for this `R`-module structure, and the ideal `𝔪_R S`
   is `(IsLocalRing.maximalIdeal R).map (algebraMap R S)`, the ideal generated by the image of
   `𝔪_R` under that same map.
4. Not degenerate. For `R = k⟦x⟧ → S = k⟦x, y⟧` the hypotheses hold, `S/𝔪_R S = k⟦y⟧`, and both
   sides are true with every quantity computed rather than forced: `depth(S) = dim(S) = 2`,
   `depth(R) = dim(R) = 1` and `depth(k⟦y⟧) = dim(k⟦y⟧) = 1`. Both sides also fail together, so
   neither is trivially true: for `R = k` and `S = k[x, y]_{(x, y)}/(x^2, xy)`, a flat local
   `k`-algebra, the fibre is `S` itself and `depth(S) = 0 < 1 = dim(S)`.

`IsNoetherianRing R` is not assumed, although the source assumes both rings Noetherian. It is a
consequence of the remaining hypotheses, so the statement is equivalent to the source's and no
weaker: a flat local homomorphism is faithfully flat
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), `S ⊗[R] R ≃ₗ[S] S` is Noetherian over `S`, and
Noetherianity of a module descends along a faithfully flat extension
(`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`). These are therefore
the hypotheses of Tag 0337, the statement this one is deduced from.

## References

* [StackProject 045J](https://stacks.math.columbia.edu/tag/045J)
* [StackProject 0337](https://stacks.math.columbia.edu/tag/0337)
* [StackProject 00ON](https://stacks.math.columbia.edu/tag/00ON)

## Tags

Cohen-Macaulay local ring, depth, flat local homomorphism, fibre ring, Krull dimension
-/


namespace Module

/-- **Cohen–Macaulayness along a flat local homomorphism.** Let `R → S` be a flat local
homomorphism of local rings with `S` Noetherian. Then `S` is Cohen–Macaulay, that is
`depth_{𝔪_S}(S) = dim(S)`, if and only if `R` is Cohen–Macaulay and the fibre ring `S/𝔪_R S` is
Cohen–Macaulay, the latter written as `depth_{𝔪_S}(S/𝔪_R S) = dim(S/𝔪_R S)` with the depth taken
over `S`, which is the depth of `S/𝔪_R S` as a local ring in its own right. -/
@[stacks 045J "Cohen-Macaulayness of a Noetherian local ring `A` (Definition 00N8) is \
  `Module.IsMaximalCohenMacaulay A A`, i.e. `depth_{𝔪_A}(A) = dim A`; for the fibre that \
  equation is written out, with its depth taken over `S` along `𝔪_S` as in Tag 0337, since a \
  quotient of a local ring carries no `IsLocalRing` instance. `IsNoetherianRing R` is dropped, \
  being a consequence of faithful flatness. See the module docstring.",
  ega "IV 6.3.5" "CM clauses of (i),(ii)", ega "IV 15.4.2" "partial", ega "IV 6.3.3" "Case M = A"]
public theorem isMaximalCohenMacaulay_self_iff_of_flat (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    IsMaximalCohenMacaulay S S ↔
      IsMaximalCohenMacaulay R R ∧
        (depth S (IsLocalRing.maximalIdeal S)
              (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) : WithBot ℕ∞) =
          ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) :=
    by apply Stacks.CohenMacaulay.FlatFibreCriterion.solution

end Module

