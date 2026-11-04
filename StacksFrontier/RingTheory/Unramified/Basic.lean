module

public import Mathlib.Algebra.Colimit.Ring
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
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Unramified.Defs
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

-- The former @[stacks 00UN] declaration is now the Mathlib class and its characterization.
add_to_stacks 00UN "formally unramified ring maps" Algebra.FormallyUnramified
add_to_sga "3 XI 1.1" Algebra.FormallyUnramified
add_to_ega "IV 17.1.1" Algebra.FormallyUnramified
add_to_sga "3 XI 1.6" "affine case, unramified" Algebra.FormallyUnramified
add_to_ega "0 19.10.2" "discrete, unramified" Algebra.FormallyUnramified
add_to_stacks 00UN "at most one dotted arrow, as injectivity of post-composition"
  Algebra.FormallyUnramified.iff_comp_injective
add_to_sga "3 XI 1.1" "partial" Algebra.FormallyUnramified.iff_comp_injective
add_to_ega "0 19.10.4" "partial, special case" Algebra.FormallyUnramified.iff_comp_injective
add_to_ega "IV 17.1.1" "special case" Algebra.FormallyUnramified.iff_comp_injective
add_to_sga "3 XI 1.6" "affine case, unramified" Algebra.FormallyUnramified.iff_comp_injective
add_to_ega "0 19.10.2" "discrete, unramified" Algebra.FormallyUnramified.iff_comp_injective

-- The former @[stacks 00UO] declaration is now the Mathlib theorem.
add_to_stacks 00UO "formally unramified iff the module of differentials vanishes"
  Algebra.formallyUnramified_iff
add_to_ega "IV 17.2.1" "affine case" Algebra.formallyUnramified_iff
add_to_ega "0 21.7.4" "b) ⇔ d)" Algebra.formallyUnramified_iff
add_to_ega "IV 17.4.1" "(c) <=> (e)" Algebra.formallyUnramified_iff
add_to_ega "0 20.7.4" "discrete case"
  Algebra.formallyUnramified_iff
add_to_ega "0 21.7.4" "b) <=> d)" Algebra.formallyUnramified_iff
add_to_ega "IV 17.2.1" "affine/ring case" Algebra.formallyUnramified_iff

-- The former @[stacks 04E9] declarations are now the Mathlib theorems.
add_to_stacks 04E9 "(1)" Algebra.FormallyUnramified.localization_map
add_to_stacks 04E9 "(2), together with `Algebra.FormallyUnramified.comp`"
  Algebra.FormallyUnramified.of_isLocalization
add_to_ega "0 19.10.3" "partial" Algebra.FormallyUnramified.of_isLocalization

-- The former @[stacks 0H91] declaration is now the Mathlib instance.
add_to_stacks 0H91 "formal unramifiedness is stable under base change"
  Algebra.FormallyUnramified.base_change
add_to_sga "3 XI 1.6" "partial" Algebra.FormallyUnramified.base_change
add_to_ega "IV 17.1.3" "(iii), special case" Algebra.FormallyUnramified.base_change
add_to_ega "IV 17.7.3" "(i), (ii)" Algebra.FormallyUnramified.base_change

@[expose] public section

/-!
# Étale ring maps are the flat G-unramified ones

Proof of `Algebra.Etale.tfae` (Stacks 08WD): for a ring map `R → S` the three conditions

1. `R → S` is étale,
2. `R → S` is flat and G-unramified,
3. `R → S` is flat, unramified and of finite presentation

are equivalent.

An étale algebra is of finite presentation by definition, and it is flat and formally unramified,
so it is G-unramified. Conversely a flat algebra of finite presentation whose module of
differentials vanishes is étale: formal unramifiedness kills the differentials of the naive
cotangent complex and flatness kills its first homology, so that complex is quasi-isomorphic to
zero. That is the equivalence of (1) and (2). Items (2) and (3) then differ only in which
finiteness condition is named where: G-unramifiedness is formal unramifiedness with finite
presentation and unramifiedness is formal unramifiedness with finite type, so in the presence of
the separate conjunct of finite presentation — which implies finite type — the two conjunctions
have the same content.

## Main results

* `Stacks.Unramified.EtaleFlatCriterion.solution`: the statement of Stacks 08WD, as one
  `List.TFAE`.

## Implementation notes

*The mathematics is `etale_iff_flat_and_gUnramified`, the equivalence of (1) and (2).* It is the
algebra-level form of Mathlib's `RingHom.Etale.iff_flat_and_formallyUnramified`, which Mathlib
states only for a ring map; its nontrivial direction is
`Algebra.Etale.of_formallyUnramified_of_flat`, and its other direction is the flatness of an
étale algebra, the Lean form of item (6) of Lemma 00U2. The passage from (2) to (3) is the
separate `gUnramified_iff_unramified_and_finitePresentation`, which is bookkeeping between two
classes; nothing else is left, so the two lemmas assemble into the `List.TFAE` in two steps.

*The source's route through Lemma 00U6 and Lemma 00UW is replaced by one Mathlib lemma.* The
source proves (3) ⇒ (1) prime by prime, characterizing étaleness at a prime by a standard étale
presentation (Lemma 00U6) and using the local structure of unramified maps (Lemma 00UW), then
globalizing by item (5) of Lemma 00U2. `Algebra.Etale.of_formallyUnramified_of_flat` is that
implication, proved instead through the vanishing of the first homology of the naive cotangent
complex of a flat algebra; the hypotheses and the conclusion are the same.

*The implication (1) ⇒ (2) is not taken from item (5) of Lemma 00UV.* That item says that an étale
algebra is G-unramified and unramified, which is the conjunction of formal unramifiedness with the
relevant finiteness condition; both conjuncts are found here by instance search from
`Algebra.Etale R S`, which is what the proof of that item does as well.

## References

* [Stacks 08WD](https://stacks.math.columbia.edu/tag/08WD), Lemma 10.151.8
* [Stacks 00UT](https://stacks.math.columbia.edu/tag/00UT), item (2), for `Algebra.GUnramified`
* [Stacks 00UV](https://stacks.math.columbia.edu/tag/00UV), item (5)
* [Stacks 00U2](https://stacks.math.columbia.edu/tag/00U2), item (6)
-/

@[expose] public section

namespace Stacks.Unramified.EtaleFlatCriterion

section Helpers

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- **A G-unramified algebra is exactly an unramified algebra of finite presentation**
(Stacks 00UT): both notions record the vanishing of `Ω_{S/R}` as formal unramifiedness, and finite
presentation implies finite type, so the finiteness condition carried by `Algebra.Unramified` says
nothing more once finite presentation is assumed separately. -/
private theorem gUnramified_iff_unramified_and_finitePresentation :
    Algebra.GUnramified R S ↔ Algebra.Unramified R S ∧ Algebra.FinitePresentation R S :=
  ⟨fun _ => ⟨{}, inferInstance⟩, fun ⟨_, _⟩ => {}⟩

/-- **An algebra is étale if and only if it is flat and G-unramified** (Stacks 08WD, (1) ↔ (2)).
An étale algebra is of finite presentation and formally unramified by definition and flat by item
(6) of Lemma 00U2; conversely, for a flat algebra of finite presentation the vanishing of the
differentials forces the whole naive cotangent complex to be quasi-isomorphic to zero. -/
@[sga "4½ Arcata 2.1.1"]
private theorem etale_iff_flat_and_gUnramified :
    Algebra.Etale R S ↔ Module.Flat R S ∧ Algebra.GUnramified R S :=
  ⟨fun _ => ⟨inferInstance, {}⟩, fun ⟨_, _⟩ => Algebra.Etale.of_formallyUnramified_of_flat⟩

end Helpers

/-- **Stacks 08WD.** For an `R`-algebra `S` the following are equivalent: `S` is étale over `R`;
`S` is flat and G-unramified over `R`; `S` is flat, unramified and of finite presentation over
`R`. -/
public theorem solution (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [Algebra.Etale R S,
       Module.Flat R S ∧ Algebra.GUnramified R S,
       Module.Flat R S ∧ Algebra.Unramified R S ∧ Algebra.FinitePresentation R S] := by
  tfae_have 1 ↔ 2 := etale_iff_flat_and_gUnramified R S
  tfae_have 2 ↔ 3 := and_congr_right' (gUnramified_iff_unramified_and_finitePresentation R S)
  tfae_finish

end Stacks.Unramified.EtaleFlatCriterion

end

/-!
# Étale ring maps are the flat G-unramified ones

Let `R → S` be a ring map. It is *étale* if it is of finite presentation and its naive cotangent
complex is quasi-isomorphic to zero (Definition 00U1), *unramified* if it is of finite type with
`Ω_{S/R} = 0`, and *G-unramified* if it is of finite presentation with `Ω_{S/R} = 0`
(Definition 00UT). Étale maps are flat and unramified, and conversely a flat unramified map of
finite presentation is étale: the vanishing of `Ω_{S/R}` and flatness together force the
vanishing of `H_1` of the naive cotangent complex. So being étale is the conjunction of flatness
with G-unramifiedness, which — finite presentation being present in both — is the same as
flatness, unramifiedness and finite presentation.

## Main results

* `Algebra.Etale.tfae`: the three conditions of Lemma 08WD — étale; flat and G-unramified; flat,
  unramified and of finite presentation — in the source's order, as one `List.TFAE`.

## Implementation notes

*The three items are one `List.TFAE`, in the source's order.* Item (1) is Mathlib's
`Algebra.Etale`, formal étaleness together with finite presentation, which is the source's
Definition 00U1 by its Lemma 00UR. Item (2) is flatness together with `Algebra.GUnramified`, the
class of Definition 00UT (2), whose fields are formal unramifiedness — the vanishing of
`Ω_{S/R}`, by Lemma 00UO — and finite presentation. Item (3) is flatness together with
`Algebra.Unramified`, Definition 00UT (1), and finite presentation, in the source's order.

*Flatness is `Module.Flat R S`.* That is flatness of `S` as an `R`-module along the given map,
which is what the source means by a flat ring map; Mathlib's `RingHom.Flat f` is this condition at
`f.toAlgebra`.

*Finite presentation is kept as a separate conjunct of item (3).* `Algebra.Unramified` carries
only finite type, so without that conjunct item (3) would not be the source's condition: finite
type does not imply finite presentation over a general base ring, and it is precisely this
conjunct that makes items (2) and (3) agree by definition, as the source's proof observes.

*Stated for an `R`-algebra, not for a bare ring map.* This is how Mathlib and this section's
earlier results state the notions involved; for `f : R →+* S` the statement is this one at
`f.toAlgebra`. Mathlib's `RingHom.Etale.iff_flat_and_formallyUnramified` is the ring-map form of
`(1) ↔ (2)` with G-unramifiedness unfolded into its two fields.

Faithfulness to [Stacks 08WD]. (1) No hypothesis is idle: the only hypotheses are the two
commutative ring structures and the algebra structure, which are the ring map of the statement,
and each occurs in every item; nothing is assumed about `R` or `S` beyond that — no Noetherian,
finiteness or flatness hypothesis — and the finiteness and flatness conditions are asserted
inside the items, where the source puts them. (2) The scalars and the base are the source's:
flatness, finite type, finite presentation, formal étaleness and the vanishing of the
differentials are all taken over `R`, the source of the given map, not over a localization of `R`
and not over `S`. (3) The canonical map is pinned: the instance `Algebra R S` *is* the map
`R → S`, and every item is a condition on that map, so no other algebra structure on `S` can
satisfy the statement. (4) The instantiation is not degenerate: all three items hold for `R → R`
and fail for `R → R[X]` over a nonzero `R`; `ℚ → ℚ[X]` is flat and of finite presentation but
neither unramified nor étale, its differentials being free of rank one, while `ℤ → ℤ/2ℤ` is
G-unramified — a surjection, so of finite presentation with vanishing differentials — and neither
flat nor étale. So no item is implied by a proper part of another item's conjunction, and the
equivalence is not an equivalence of two conditions that always hold or always fail.

## References

* [Stacks 08WD](https://stacks.math.columbia.edu/tag/08WD), Lemma 10.151.8, in Section 10.151
  "Unramified ring maps" (Section 00US). Étale is Definition [Stacks 00U1], in Section 00U0
  "Étale ring maps", and unramified and G-unramified are Definition 10.151.1 = [Stacks 00UT]; the
  identification of `Ω_{S/R} = 0` with formal unramifiedness is Lemma 00UO, and that of étale with
  formally étale of finite presentation is Lemma 00UR, which is stated there for a map of finite
  presentation.
-/

@[expose] public section

/-- **Stacks 08WD.** Let `R → S` be a ring map. The following are equivalent:

1. `R → S` is étale;
2. `R → S` is flat and G-unramified;
3. `R → S` is flat, unramified, and of finite presentation. -/
@[stacks 08WD "The three items are the entries, in the source's order, of one `List.TFAE`. Étale
is Mathlib's `Algebra.Etale`, formally étale plus finite presentation, which is the source's
Definition 00U1 by its Lemma 00UR; flat is `Module.Flat R S`; G-unramified and unramified are
`Algebra.GUnramified` and `Algebra.Unramified` (Definition 00UT). See the module docstring."]
public theorem Algebra.Etale.tfae (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [Algebra.Etale R S,
       Module.Flat R S ∧ Algebra.GUnramified R S,
       Module.Flat R S ∧ Algebra.Unramified R S ∧ Algebra.FinitePresentation R S] :=
    by apply Stacks.Unramified.EtaleFlatCriterion.solution

end

end

@[expose] public section


/-- Formally unramified is a local property: for a ring map `R → S`, being formally
unramified is equivalent to all the localized maps `R → S_𝔮` being formally
unramified, which in turn is equivalent to all the maps `R_𝔭 → S_𝔮` (with
`𝔭 = R ∩ 𝔮`) being formally unramified. -/
@[stacks 04E8, ega "IV 17.4.2" "Affine case of a ⇔ e"]
theorem formally_unramified_local
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    List.TFAE
      [ Algebra.FormallyUnramified R S,
        ∀ (𝔮 : Ideal S) [𝔮.IsPrime],
          Algebra.FormallyUnramified R (Localization.AtPrime 𝔮),
        ∀ (𝔮 : Ideal S) [𝔮.IsPrime],
          haveI : (𝔮.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
          haveI : 𝔮.LiesOver (𝔮.comap (algebraMap R S)) := ⟨rfl⟩
          haveI : Algebra (Localization.AtPrime (𝔮.comap (algebraMap R S)))
              (Localization.AtPrime 𝔮) := Localization.AtPrime.algebraOfLiesOver _ 𝔮
          Algebra.FormallyUnramified
            (Localization.AtPrime (𝔮.comap (algebraMap R S)))
            (Localization.AtPrime 𝔮) ] := by
  tfae_have h12 : 1 → 2 := fun _ 𝔮 _ =>
    Algebra.FormallyUnramified.comp R S (Localization.AtPrime 𝔮)
  tfae_have h21 : 2 → 1 := by
    intro h
    rw [Algebra.formallyUnramified_iff]
    apply Module.subsingleton_of_localization_maximal
      (fun (P : Ideal S) [P.IsMaximal] => Ω[(Localization.AtPrime P)⁄R])
      (fun (P : Ideal S) [P.IsMaximal] => KaehlerDifferential.map R R S (Localization.AtPrime P))
    intro P hP
    have : P.IsPrime := hP.isPrime
    have := h P
    exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  tfae_have h23 : 2 ↔ 3 := by
    refine forall_congr' fun 𝔮 => forall_congr' fun _ => ?_
    have : (𝔮.comap (algebraMap R S)).IsPrime := Ideal.IsPrime.comap _
    have : 𝔮.LiesOver (𝔮.comap (algebraMap R S)) := ⟨rfl⟩
    let : Algebra (Localization.AtPrime (𝔮.comap (algebraMap R S)))
        (Localization.AtPrime 𝔮) := Localization.AtPrime.algebraOfLiesOver _ 𝔮
    refine ⟨fun h => Algebra.FormallyUnramified.localization_base
      (𝔮.comap (algebraMap R S)).primeCompl, fun h => ?_⟩
    have : Algebra.FormallyUnramified R
        (Localization.AtPrime (𝔮.comap (algebraMap R S))) := by
      grind only [Algebra.FormallyUnramified.iff_comp_injective,
        Algebra.FormallyUnramified.comp_injective]
    exact Algebra.FormallyUnramified.comp R
      (Localization.AtPrime (𝔮.comap (algebraMap R S))) (Localization.AtPrime 𝔮)
  tfae_finish

end

/-!
# A directed colimit of formally unramified algebras is formally unramified

Let `R` be a commutative ring and `ι` a nonempty directed preorder. Let `(S i, φ i j)`
be a directed system of `R`-algebras over `ι` and let `S = colim_{i ∈ ι} S i` be its
directed colimit as an `R`-algebra, with canonical `R`-algebra maps `ι_i : S i →ₐ[R] S`.
If `R → S i` is formally unramified for every `i`, then `S` is formally unramified over
`R`.

Formal unramifiedness is `Algebra.FormallyUnramified`, characterized by
`Algebra.FormallyUnramified.iff_comp_injective`: for every square-zero ideal `I ⊆ B` and
every `R`-algebra map `f : A → B ⧸ I` there is at most one lift to an `R`-algebra map
`A → B`. A directed system over `ι` consists of `R`-algebras `S i` with `R`-algebra
transition maps `φ i j : S i →ₐ[R] S j` for `i ≤ j`, compatible with composition;
`DirectedSystem` records the compatibility of the underlying maps and
`Ring.DirectLimit` is the colimit.

## Main results

The argument needs only part of the colimit data: an `R`-algebra `T` with a jointly
surjective family of `R`-algebra maps `ι_i : S i →ₐ[R] T`. The abstract form
`Algebra.FormallyUnramified.of_jointly_surjective` is stated at that level of generality,
and `Algebra.FormallyUnramified.directLimit` specializes it to `Ring.DirectLimit`.

The direct limit carries the canonical `R`-algebra structure `directLimitAlgebra φ`,
whose structure map `R → DirectLimit` is `Ring.DirectLimit.of i₀ ∘ algebraMap R (S i₀)`
for a basepoint `i₀`. By directedness this is independent of the basepoint, so each
canonical map `Ring.DirectLimit.of … i` is automatically an `R`-algebra homomorphism
(`Ring.DirectLimit.of_commutes`) and the concrete statement needs no extra
compatibility hypothesis.
-/

@[expose] public section

section Abstract

variable {ι : Type*} {R : Type*} [CommRing R]
variable {S : ι → Type*} [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
variable {T : Type*} [CommRing T] [Algebra R T]
variable (ιmap : (i : ι) → S i →ₐ[R] T)

/-- **Abstract form.** Let `T` be an `R`-algebra equipped with a jointly surjective
family of `R`-algebra maps `ιmap i : S i →ₐ[R] T` (every element of `T` is `ιmap i x`
for some `i` and `x`). If every `S i` is formally unramified over `R`, then so is `T`.
This applies in particular to the directed colimit of formally unramified algebras. -/
@[ega "0 19.10.3" "more general"]
theorem Algebra.FormallyUnramified.of_jointly_surjective
    (hsurj : ∀ s : T, ∃ (i : ι) (x : S i), ιmap i x = s)
    (hunram : ∀ i, Algebra.FormallyUnramified R (S i)) :
    Algebra.FormallyUnramified R T := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI g₁ g₂ hg
  ext s
  obtain ⟨i, x, rfl⟩ := hsurj s
  have := hunram i
  exact AlgHom.congr_fun (Algebra.FormallyUnramified.ext (R := R) I ⟨2, hI⟩
    (g₁ := g₁.comp (ιmap i)) (g₂ := g₂.comp (ιmap i))
    fun y => by simpa using AlgHom.congr_fun hg (ιmap i y)) x

end Abstract

section Concrete

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable {R : Type*} [CommRing R]
variable {S : ι → Type*} [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
variable (φ : (i j : ι) → i ≤ j → S i →ₐ[R] S j)

/-- The canonical `R`-algebra structure on `Ring.DirectLimit S φ` for a directed
system of `R`-algebras. The structure map `R → DirectLimit` is
`Ring.DirectLimit.of i₀ ∘ algebraMap R (S i₀)` for a basepoint `i₀`; by directedness
this is independent of the basepoint, so the structure is the unique one for which
every `Ring.DirectLimit.of … i` is an `R`-algebra homomorphism (see
`Ring.DirectLimit.of_commutes`). -/
@[reducible] noncomputable def directLimitAlgebra :
    Algebra R (Ring.DirectLimit S (fun i j h => (φ i j h : S i → S j))) :=
  ((Ring.DirectLimit.of S (fun i j h => (φ i j h : S i → S j)) (Classical.arbitrary ι)).comp
    (algebraMap R (S (Classical.arbitrary ι)))).toAlgebra

/-- **Correctness of `directLimitAlgebra`.** For the canonical `R`-algebra structure
`directLimitAlgebra φ` on the direct limit, every canonical map
`Ring.DirectLimit.of … i` is an `R`-algebra homomorphism, i.e. it commutes with the
structure maps from `R`. This is automatic (no hypothesis), so it pins down the
algebra structure as the correct colimit structure. -/
theorem Ring.DirectLimit.of_commutes (i : ι) (r : R) :
    letI := directLimitAlgebra φ
    (Ring.DirectLimit.of S (fun i j h => (φ i j h : S i → S j)) i) (algebraMap R (S i) r)
      = algebraMap R (Ring.DirectLimit S (fun i j h => (φ i j h : S i → S j))) r := by
  let := directLimitAlgebra φ
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  obtain ⟨k, hik, hi₀k⟩ := IsDirected.directed (r := (· ≤ ·)) i (Classical.arbitrary ι)
  rw [← Ring.DirectLimit.of_f (f := fun i j h => (φ i j h : S i → S j)) hik,
    ← Ring.DirectLimit.of_f (f := fun i j h => (φ i j h : S i → S j)) hi₀k]
  simp

/-- **Concrete `Ring.DirectLimit` form.** Equip the direct limit
`Ring.DirectLimit S φ` of a directed system of `R`-algebras with its canonical
`R`-algebra structure `directLimitAlgebra φ`. If every `S i` is formally unramified
over `R`, then so is the direct limit. (No extra compatibility hypothesis is needed:
the canonical maps `Ring.DirectLimit.of … i` are automatically `R`-algebra
homomorphisms, cf. `Ring.DirectLimit.of_commutes`.) -/
@[stacks 07QE]
theorem Algebra.FormallyUnramified.directLimit
    [DirectedSystem S (fun i j h => (φ i j h : S i → S j))]
    (hunram : ∀ i, Algebra.FormallyUnramified R (S i)) :
    letI := directLimitAlgebra φ
    Algebra.FormallyUnramified R (Ring.DirectLimit S (fun i j h => (φ i j h : S i → S j))) := by
  let := directLimitAlgebra φ
  let ιmap : (i : ι) → S i →ₐ[R] Ring.DirectLimit S (fun i j h => (φ i j h : S i → S j)) := fun i =>
    { Ring.DirectLimit.of S (fun i j h => (φ i j h : S i → S j)) i with
      commutes' := Ring.DirectLimit.of_commutes φ i }
  exact Algebra.FormallyUnramified.of_jointly_surjective ιmap Ring.DirectLimit.exists_of hunram

end Concrete

end
