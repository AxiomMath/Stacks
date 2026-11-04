module

import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.Tactic.ENatToNat

import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- Stacks tag 00TB: https://stacks.math.columbia.edu/tag/00TB


/-- A ring map `R → S` is *smooth at a prime* `q` of `S` if there exists
some `g ∈ S` with `g ∉ q` such that the induced map `R → S_g` is smooth. -/
@[stacks 00TB, sga "1 II 1.1"]
def Algebra.SmoothAt (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] : Prop :=
  ∃ (g : S), g ∉ q ∧ Algebra.Smooth R (Localization.Away g)

/-- `Algebra.SmoothAt` unfolded: `R → S` is smooth at the prime `q` exactly when some
`g ∈ S` with `g ∉ q` has `R → S_g` smooth. -/
theorem Algebra.smoothAt_iff (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.SmoothAt R S q ↔
      ∃ (g : S), g ∉ q ∧ Algebra.Smooth R (Localization.Away g) :=
  Iff.rfl

/-!
# Smoothness of a ring map is detected at the primes of the target

This file proves Stacks 00TC: a ring
map `R → S` is smooth if and only if it is smooth at every prime `𝔮` of `S`, i.e. if and only if
for every prime `𝔮` there is a `g ∉ 𝔮` with `R → S_g` smooth (Definition 00TB).

The forward direction is trivial, with `g = 1`. For the converse, the two halves of smoothness are
produced separately from the pointwise hypothesis. The elements `g` for which `S_g` is smooth over
`R` generate the unit ideal, since a proper ideal is contained in a maximal one and the hypothesis
supplies such a `g` outside it; finite presentation of `S` over `R` then descends along that
standard covering. Once `S` is of finite presentation, smoothness is the vanishing of the
obstruction on the whole of `Spec(S)`, and the hypothesis puts every prime in a standard open
`D(g)` on which the obstruction vanishes.

## Implementation notes

*The route departs from the source's, which is longer than it needs to be.* The source's proof
extracts a finite covering from the quasi-compactness of `Spec(S)` (Lemma 00E8), gets finite
presentation from Lemma 00EP, and then glues the naive cotangent complex with Lemmas 00S7 and 00NX.
No finiteness of the covering is needed: the descent of finite presentation along an arbitrary
standard covering of the target is `Algebra.FinitePresentation.of_span_eq_top_target`, which is
Lemma 00EP without the finiteness hypothesis, and the gluing of `NL_{S/R}` is
`Algebra.basicOpen_subset_smoothLocus_iff_smooth`, in which the content of Lemmas 00S7 and 00NX is
already packaged as the statement that `D(g) ⊆ smoothLocus R S` holds exactly when `S_g` is smooth
over `R` — the smooth locus being the complement of the support of `H₁(L_{S/R})` intersected with
the free locus of `Ω_{S/R}`, which is where 00NX's characterization of finite projectivity by the
free locus and 00S7's compatibility of `NL` with localization enter. Consequently neither imported
statement is used, and the last step is a single `basicOpen` membership rather than a gluing
argument.

*The spanning step is prime avoidance, not quasi-compactness.* It is isolated as
`span_eq_top_iff_forall_isMaximal_exists_notMem`, an `Iff` over an arbitrary commutative semiring
with the hypothesis only on maximal ideals; Mathlib has `Ideal.ne_top_iff_exists_maximal` but no
spelling of this criterion for a spanning set.

## References

* [Stacks 00TC](https://stacks.math.columbia.edu/tag/00TC), Lemma 10.137.12
-/

namespace Stacks.Smooth.PointwiseCriterion

/-- A set generates the unit ideal exactly when it is contained in no maximal ideal, i.e. when
every maximal ideal is avoided by some element of the set. -/
private theorem span_eq_top_iff_forall_isMaximal_exists_notMem {R : Type*} [CommSemiring R]
    (s : Set R) : Ideal.span s = ⊤ ↔ ∀ q : Ideal R, q.IsMaximal → ∃ g ∈ s, g ∉ q := by
  refine ⟨fun hs q hq => ?_, fun h => ?_⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hq.ne_top (top_le_iff.mp (hs.ge.trans (Ideal.span_le.mpr hcon)))
  · by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgs, hgq⟩ := h q hq
    exact hgq (hle (Ideal.subset_span hgs))

/-- A ring map `R → S` is smooth if and only if every prime `q` of `S` admits some `g ∉ q` such
that `R → S_g` is smooth. -/
public theorem solution (R : Type*) [CommRing R] (S : Type*)
    [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      ∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) := by
  refine ⟨fun h q hq => ⟨1, fun h1 => hq.ne_top (Ideal.eq_top_of_isUnit_mem q h1 isUnit_one), ?_⟩,
    fun h => ?_⟩
  · have : Algebra.Smooth S (Localization.Away (1 : S)) :=
      Algebra.Smooth.of_isLocalization_Away (1 : S)
    exact .comp R S _
  · have hfp : Algebra.FinitePresentation R S := by
      refine Algebra.FinitePresentation.of_span_eq_top_target
        {g : S | Algebra.Smooth R (Localization.Away g)}
        ((span_eq_top_iff_forall_isMaximal_exists_notMem _).mpr fun q hq => ?_)
        fun i hi => hi.finitePresentation
      obtain ⟨g, hgq, hg⟩ := h q
      exact ⟨g, hg, hgq⟩
    refine ⟨?_, hfp⟩
    rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro p
    obtain ⟨g, hgp, hg⟩ := h p.asIdeal
    exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hg
      ((PrimeSpectrum.mem_basicOpen g p).mpr hgp)

end Stacks.Smooth.PointwiseCriterion

/-!
# Smoothness of a ring map is detected at the primes of the target

Let `R → S` be a ring map. Recall (Definition 00TB) that `R → S` is *smooth at* a prime `q ⊂ S`
if there is a `g ∈ S`, `g ∉ q`, such that `R → S_g` is smooth. Then `R → S` is smooth if and only
if it is smooth at every prime of `S`.

One direction is trivial: if `R → S` is smooth take `g = 1`. For the converse, `Spec(S)` is
quasi-compact (Lemma 00E8), so the standard opens `D(g)` with `S_g` smooth over `R` — which by
hypothesis cover `Spec(S)` — admit a finite subcover `Spec(S) = ⋃ D(g_i)`. Finiteness is what makes
the two ingredients of smoothness descend: `S` is of finite presentation over `R` by Lemma 00EP,
and `NL_{S/R} ⊗_S S_{g_i}` is quasi-isomorphic to a finite projective `S_{g_i}`-module in degree
`0` (Lemma 00S7), whence `NL_{S/R}` is quasi-isomorphic to a finite projective `S`-module in degree
`0` by Lemma 00NX.

## Main results

* `Algebra.smooth_iff_forall_exists_notMem_smooth`: a ring map is smooth if and only if it is
  smooth at every prime of the target, 00TC.

## Implementation notes

*The right-hand side spells out Definition 00TB rather than citing Mathlib's `Algebra.IsSmoothAt`.*
Mathlib's `Algebra.IsSmoothAt R q` is `Algebra.FormallySmooth R S_q`, which carries no finiteness,
and with it in place of the source's definition the equivalence is **false**: for `R = k` a field
and `S = k[x_i : i ∈ ℕ]` every `S_q` is formally smooth over `k` (a free algebra is formally smooth
and `S → S_q` is formally étale, so `Algebra.FormallySmooth.comp` applies), while
`Algebra.Smooth k S` fails for want of finite presentation. The two definitions agree exactly when
`S` is of finite presentation over `R` (`Algebra.basicOpen_subset_smoothLocus_iff_smooth` together
with `Algebra.isOpen_smoothLocus`, as that abbreviation's docstring records), and producing that
finite presentation from the pointwise hypothesis is the content of this lemma — so citing
`IsSmoothAt` here would assume what is to be proved. Under a finite presentation hypothesis the
statement instead becomes Mathlib's `Algebra.smoothLocus_eq_univ_iff`; no such hypothesis is added,
since the source has none.

*Localizations are the concrete `Localization.Away g`.* This is Mathlib's spelling of the very same
existential in `Algebra.IsSmoothAt.exists_notMem_smooth`, and nothing is lost: for any `Sg` with
`IsLocalization.Away g Sg`, `IsLocalization.algEquiv` and `Algebra.Smooth.of_equiv` transfer
smoothness. The `R`-algebra structure on `Localization.Away g` is the one through `S`, so the
statement is about the composite `R → S → S_g` as the source is.

*Stated for algebras rather than for a bundled `f : R →+* S`.* `RingHom.smooth_algebraMap` turns
this into the statement for `algebraMap R S`, and every ring map is such an `algebraMap`. The name
mutates the Mathlib sibling `Algebra.IsSmoothAt.exists_notMem_smooth`, whose conclusion is the
right-hand side here.

Faithfulness. (1) No hypothesis is dead: apart from the ring and algebra structures there is none
— in particular no finite presentation, no Noetherian, and no finiteness on the covering, all of
which would make the lemma a different (weaker) statement. (2) The scalars and the base are the
source's: smoothness is over `R` itself on both sides, `q` ranges over the primes of the target `S`
(not over primes of `R`), and `S_g` is a localization of `S` regarded as an `R`-algebra through
`R → S`. (3) The canonical maps are pinned rather than merely asserted to exist: the right-hand
side is not "some smooth `R`-algebra localizes `S`" but that the localization `S_g` of `S` at the
element `g`, with its `R`-algebra structure through `S`, is smooth over `R`. (4) The instantiation
is not degenerate: `R → R[x]` satisfies both sides (`g = 1` at every prime), and `k → k[x]/(x²)`
fails both (its only prime is `(x)`, and any `g ∉ (x)` is a unit, so `S_g ≅ S`, which is not smooth
over `k`), so neither direction is vacuous.

## References

* [Stacks 00TC](https://stacks.math.columbia.edu/tag/00TC), Lemma 10.137.12
  (`algebra-lemma-locally-smooth`), in Section 10.137 "Smooth ring maps". Definition 00TB of
  smoothness at a prime is spelled out on the right-hand side, and the source's proof uses
  Lemma 00E8 (`Spec(S)` is quasi-compact), Lemma 00EP (finite presentation from a finite covering
  by standard opens), Lemma 00S7 (localization of the naive cotangent complex) and Lemma 00NX
  (a finitely presented module that is projective at each prime of a finite covering is
  projective).
-/

@[expose] public section

/-- **Smoothness is detected at the primes of the target.** A ring map `R → S` is smooth if and
only if it is smooth at every prime `q` of `S`, that is, if and only if for every prime `q ⊂ S`
there is a `g ∈ S`, `g ∉ q`, with `R → S_g` smooth (Definition 00TB).

Beware that the right-hand side is the Stacks project's notion of smoothness at `q`, which is
strictly stronger than Mathlib's `Algebra.IsSmoothAt R q = Algebra.FormallySmooth R S_q` when `S`
is not of finite presentation over `R`; see the module docstring. -/
@[stacks 00TC "Smoothness at a prime `q` (Definition 00TB) is spelled out as `∃ g ∉ q`, with
`Localization.Away g` smooth over `R` — as in Mathlib's `Algebra.IsSmoothAt.exists_notMem_smooth`
— and not as Mathlib's `Algebra.IsSmoothAt`, which is formal smoothness of `S_q` and makes the
equivalence false for `S` not of finite presentation over `R` (witness: `k[x_i : i ∈ ℕ]` over `k`).
Producing the finite presentation of `S` from the pointwise hypothesis is precisely the content of
this lemma. Stated for algebras; `RingHom.smooth_algebraMap` gives the form for a bundled ring map.
See the module docstring."]
public theorem Algebra.smooth_iff_forall_exists_notMem_smooth (R : Type*) [CommRing R] (S : Type*)
    [CommRing S] [Algebra R S] :
    Algebra.Smooth R S ↔
      ∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) :=
  Stacks.Smooth.PointwiseCriterion.solution R S

end

/-!
# Flat with a smooth fibre implies smooth, at a prime

Let `R → S` be a ring map, let `q ⊂ S` be a prime lying over `p ⊂ R`, and let `Q` be the prime of
the fibre `κ(p) ⊗_R S` corresponding to `q`. If `R → S_g` is of finite presentation for some
`g ∉ q`, if `S_q` is flat over `R` — equivalently, if `R_p → S_q` is flat — and if the fibre is
smooth over `κ(p)` at `Q`, then `R → S` is smooth at `q`: some `S_g` with `g ∉ q` is smooth
over `R`.

## Main results

* `Stacks.Smooth.FlatFibreCriterion.solution`: the statement of
  `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber`, Stacks 00TF.

## Implementation notes

The three hypotheses are conditions at `q`, so the content of the lemma is local at `q`, and it
splits in two: smoothness at `q` itself (`isSmoothAt_map_of_isSmoothAt_fiber`), and the passage
from smoothness at `q` to Definition 00TB (`exists_notMem_smooth_of_isSmoothAt_map`).

*Smoothness at `q`.* This is the local form of `Algebra.IsSmoothAt.of_formallySmooth_fiber`, whose
hypotheses are flatness of `S` over `R` and formal smoothness of the *whole* fibre; neither is
available. `formallySmooth_residueField_tensor_of_isSmoothAt_fiber` identifies the local ring of
the fibre at `Q` with `κ(p) ⊗_{R_p} S_q`, and so turns smoothness of the fibre at the single prime
`Q` into formal smoothness of `κ(p) ⊗_{R_p} S_q` over `κ(p)`; that is the hypothesis of
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor`, which is the mathematical heart and
needs only flatness of `R_p → S_q`.
`formallySmooth_of_flat_of_formallySmooth_residueField_tensor` is Mathlib's proof of
`Algebra.IsSmoothAt.of_formallySmooth_fiber` with those two global hypotheses replaced by their
values at `q`, and with the local ring `S_q` left as an arbitrary localization `Sq` of `S` at `q`
rather than the model `Localization.AtPrime q`. That generality is what makes the finite
presentation hypothesis usable: it is applied with `S` replaced by `S_g`, `q` by the prime `q S_g`,
and `Sq` still the *same* ring `S_q`, so no hypothesis has to be transported along an isomorphism.
What licenses that application is `isLocalization_atPrime_map_of_notMem`: for `g ∉ q` the local
ring `S_q` is also the local ring of `S_g` at the prime `q S_g`. Mathlib has
`IsLocalization.isLocalization_of_submonoid_le`, which gives `S_q` as the localization of `S_g` at
the *image* of `q.primeCompl`; passing from that image to `(q S_g).primeCompl` is the missing step,
and it holds because every element of the latter becomes, after multiplication by a power of `g`,
an element of the former.

*From smoothness at `q` to the conclusion.* `Algebra.IsSmoothAt.exists_notMem_smooth` produces an
element of `S_g`, not of `S`. Writing that element as `a / g^n` with `a ∈ S`
(`IsLocalization.Away.sec`), the localization of `S_g` at it is the localization of `S` at `g a`
(`IsLocalization.Away.mul_of_associated`), which is the element of `S` the conclusion asks for.

The source's route is not the one taken here. It replaces `S` by an `S_g` which is a relative
global complete intersection (Lemmas 00SY and 00T5) and then reads both smoothness of `R → S` at
`q` and smoothness of the fibre at `Q` off the same Jacobian minors (Lemma 00TE), the point being
that the minors of the presentation reduce to the minors of the reduced presentation of the fibre.
The route above replaces that comparison of presentations by the comparison of naive cotangent
complexes that `Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` already carries out;
it needs no presentation, and in particular no complete intersection.

## References

* [Stacks 00TF](https://stacks.math.columbia.edu/tag/00TF), Lemma 10.137.16.
-/

namespace Stacks.Smooth.FlatFibreCriterion

open TensorProduct IsLocalRing

/-- The local ring of the fibre `κ(p) ⊗_R S` at a prime `Q` is `κ(p) ⊗_{R_p} S_q`, where `q` is
the prime of `S` corresponding to `Q`. So smoothness of the fibre at `Q` is formal smoothness of
`κ(p) ⊗_{R_p} S_q` over `κ(p)`. -/
private lemma formallySmooth_residueField_tensor_of_isSmoothAt_fiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    [Algebra.IsSmoothAt p.ResidueField Q] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (hq : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) = q) :
    Algebra.FormallySmooth p.ResidueField
      (p.ResidueField ⊗[Localization.AtPrime p] Localization.AtPrime q) := by
  subst hq
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.extendScalarsOfSurjective residue_surjective
    ((((Ideal.Fiber.localizationAlgEquivQuotient p Q).trans
      (Ideal.quotientEquivAlgOfEq (Localization.AtPrime p)
        (Stacks.Etale.SeparableResidueAtPrime.map_algebraMap_eq_map_maximalIdeal p _))).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot _
        (maximalIdeal (Localization.AtPrime p))).restrictScalars
          (Localization.AtPrime p))).trans (Algebra.TensorProduct.comm _ _ p.ResidueField)))

/-- A prime avoiding `a` stays prime in the localization away from `a`. -/
public lemma isPrime_map_algebraMap_of_notMem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {a : A} [IsLocalization.Away a B] (p : Ideal A) [p.IsPrime]
    (ha : a ∉ p) : (p.map (algebraMap A B)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (.powers a) _ _ inferInstance
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr ha)

/-- Localizing away from `a ∉ p` and then at the extended prime is localizing at `p`: a model of
the localization of `A` at `p` is also a model of the localization of `A[1/a]` at `p·A[1/a]`. -/
public lemma isLocalization_atPrime_map_of_notMem {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] {a : A} [IsLocalization.Away a B] {p : Ideal A} [p.IsPrime]
    (ha : a ∉ p) [Algebra A C] [IsLocalization.AtPrime C p] [Algebra B C]
    [IsScalarTower A B C] [(p.map (algebraMap A B)).IsPrime] :
    IsLocalization.AtPrime C (p.map (algebraMap A B)) := by
  have hle : Submonoid.powers a ≤ p.primeCompl := Submonoid.powers_le.mpr ha
  have hcomap : (p.map (algebraMap A B)).comap (algebraMap A B) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) _ inferInstance
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr ha)
  have : IsLocalization (Submonoid.map (algebraMap A B) p.primeCompl) C :=
    IsLocalization.isLocalization_of_submonoid_le B C (Submonoid.powers a) p.primeCompl hle
  refine IsLocalization.isLocalization_of_is_exists_mul_mem C
    (Submonoid.map (algebraMap A B) p.primeCompl) _ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hcomap ▸ Ideal.mem_comap.mpr hmem)
  · intro x
    refine ⟨algebraMap A B (a ^ (IsLocalization.Away.sec a (x : B)).2), _, ?_,
      by rw [mul_comm]; exact (IsLocalization.Away.sec_spec a (x : B)).symm⟩
    intro hmem
    have hx : algebraMap A B (IsLocalization.Away.sec a (x : B)).1 ∈
        p.map (algebraMap A B) := Ideal.mem_map_of_mem _ hmem
    rw [← IsLocalization.Away.sec_spec a (x : B)] at hx
    rcases (inferInstance : (p.map (algebraMap A B)).IsPrime).mem_or_mem hx with h | h
    · exact x.2 h
    · exact hle ⟨_, rfl⟩ (hcomap ▸ Ideal.mem_comap.mpr h)

/-- **Stacks 00TF, localized at `q`.** Let `R → S` be of finite presentation, let `q` be a prime of
`S` lying over `p`, and let `Sq` be a localization of `S` at `q`. If `S_q` is flat over `R` and
`κ(p) ⊗_{R_p} S_q` is formally smooth over `κ(p)`, then `S_q` is formally smooth over `R`.

This is `Algebra.IsSmoothAt.of_formallySmooth_fiber` with `Module.Flat R S` and formal smoothness
of the whole fibre `κ(p) ⊗_R S` replaced by their values at `q`; the proof is Mathlib's, since it
only ever uses flatness of `R_p → S_q`. -/
@[ega "0 19.7.1" "b ⇒ a"]
private lemma formallySmooth_of_flat_of_formallySmooth_residueField_tensor {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (p : Ideal R)
    [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] (Sq : Type*) [CommRing Sq]
    [Algebra S Sq] [IsLocalization.AtPrime Sq q] [Algebra R Sq] [IsScalarTower R S Sq]
    [Algebra (Localization.AtPrime p) Sq] [IsScalarTower R (Localization.AtPrime p) Sq]
    [IsLocalRing Sq] [IsLocalHom (algebraMap (Localization.AtPrime p) Sq)] [Module.Flat R Sq]
    [Algebra.FormallySmooth (ResidueField (Localization.AtPrime p))
      (ResidueField (Localization.AtPrime p) ⊗[Localization.AtPrime p] Sq)] :
    Algebra.FormallySmooth R Sq := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have : Module.Flat Rp Sq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr ‹_›
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
      (M := Algebra.algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    exact IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap R S x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
      (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have := Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (R := Rp) (S := Sq) (P := Sp) (Algebra.algebraMapSubmonoid _ q.primeCompl)
  exact .comp R Rp Sq

/-- **Stacks 00TF at `q`.** With the hypotheses of 00TF and `g ∉ q` such that `R → S_g` is of
finite presentation, `R → S_g` is smooth at the prime `q S_g`.

This is the whole content of 00TF; what is left is Definition 00TB. Both halves of the criterion
are applied to `S_g` rather than to `S`, with the *same* local ring `S_q`, which is licensed by
`isLocalization_atPrime_map_of_notMem`. -/
private lemma isSmoothAt_map_of_isSmoothAt_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    [Algebra.IsSmoothAt p.ResidueField Q] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    (hq : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) = q)
    {g : S} (hgq : g ∉ q) [Algebra.FinitePresentation R (Localization.Away g)]
    [(Ideal.map (algebraMap S (Localization.Away g)) q).IsPrime] :
    Algebra.IsSmoothAt R (Ideal.map (algebraMap S (Localization.Away g)) q) := by
  have : q.LiesOver p := by subst hq; infer_instance
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  -- Hypothesis (3), read as formal smoothness of `κ(p) ⊗_{R_p} S_q` over `κ(p)`.
  have := formallySmooth_residueField_tensor_of_isSmoothAt_fiber p Q q hq
  -- The prime `q S_g` lies over `p`, and `S_q` is the local ring of `S_g` at it.
  have : (Ideal.map (algebraMap S (Localization.Away g)) q).LiesOver q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers g) _
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgq)
  have : (Ideal.map (algebraMap S (Localization.Away g)) q).LiesOver p := .trans _ q _
  let : Algebra (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers g) q.primeCompl
      (Submonoid.powers_le.mpr hgq)
  have : IsScalarTower S (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower R (Localization.Away g) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  have : IsLocalization.AtPrime (Localization.AtPrime q)
      (Ideal.map (algebraMap S (Localization.Away g)) q) :=
    isLocalization_atPrime_map_of_notMem (B := Localization.Away g)
      (C := Localization.AtPrime q) hgq
  have : Algebra.FormallySmooth R (Localization.AtPrime q) :=
    formallySmooth_of_flat_of_formallySmooth_residueField_tensor p
      (Ideal.map (algebraMap S (Localization.Away g)) q) (Localization.AtPrime q)
  exact .of_equiv ((IsLocalization.algEquiv
    (Ideal.map (algebraMap S (Localization.Away g)) q).primeCompl (Localization.AtPrime q)
      (Localization.AtPrime (Ideal.map (algebraMap S (Localization.Away g)) q))).restrictScalars R)

/-- Definition 00TB from `Algebra.IsSmoothAt`: if `R → S_g` is of finite presentation and smooth at
the prime `q S_g`, for some `g ∉ q`, then some localization of `S` itself at an element outside `q`
is smooth over `R`.

`Algebra.IsSmoothAt.exists_notMem_smooth` produces an element `f` of `S_g`; writing `f = a / g^n`
with `a ∈ S`, the localization of `S_g` at `f` is the localization of `S` at `g a`. -/
private lemma exists_notMem_smooth_of_isSmoothAt_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] {g : S} (hgq : g ∉ q)
    [Algebra.FinitePresentation R (Localization.Away g)]
    [(Ideal.map (algebraMap S (Localization.Away g)) q).IsPrime]
    [Algebra.IsSmoothAt R (Ideal.map (algebraMap S (Localization.Away g)) q)] :
    ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) := by
  obtain ⟨f, hf, hfsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R
    (Ideal.map (algebraMap S (Localization.Away g)) q)
  have hassoc := IsLocalization.Away.associated_sec_fst (S := Localization.Away g) g f
  have : IsLocalization.Away (g * (IsLocalization.Away.sec g f).1) (Localization.Away f) :=
    .mul_of_associated _ _ f hassoc
  exact ⟨g * (IsLocalization.Away.sec g f).1, ‹q.IsPrime›.mul_notMem hgq fun hmem ↦
    hf ((Ideal.mem_iff_of_associated hassoc).mp (Ideal.mem_map_of_mem _ hmem)),
    .of_equiv ((Localization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g f).1))
      (Localization.Away f)).restrictScalars R).symm⟩

/-- The statement of `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber`. -/
public theorem solution {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    [Algebra.IsSmoothAt p.ResidueField Q] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    (hq : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) = q)
    (hfp : ∃ g ∉ q, Algebra.FinitePresentation R (Localization.Away g)) :
    ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) := by
  obtain ⟨g, hgq, hfpg⟩ := hfp
  have : (Ideal.map (algebraMap S (Localization.Away g)) q).IsPrime :=
    isPrime_map_algebraMap_of_notMem q hgq
  have := isSmoothAt_map_of_isSmoothAt_fiber p Q q hq hgq
  exact exists_notMem_smooth_of_isSmoothAt_map q hgq

end Stacks.Smooth.FlatFibreCriterion

/-!
# Smoothness at a prime from flatness and a smooth fibre

Let `R → S` be a ring map and let `q ⊂ S` be a prime lying over the prime `p ⊂ R`. Assume

1. there is a `g ∈ S`, `g ∉ q`, such that `R → S_g` is of finite presentation;
2. the local ring homomorphism `R_p → S_q` is flat;
3. the fibre `S ⊗_R κ(p)` is smooth over `κ(p)` at the prime corresponding to `q`.

Then `R → S` is smooth at `q`, that is (Definition 00TB) there is a `g ∈ S`, `g ∉ q`, with
`R → S_g` smooth.

The source's proof makes the three hypotheses collapse onto one finite list of elements of `S`.
Replacing `S` by a localization `S_g`, Lemmas 00SY and 00T5 turn (1) and (2) into a presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` which is a relative global complete intersection. For a
`c`-element subset `I ⊆ {1, …, n}` put `g_I = det (∂f_j/∂x_i)_{j = 1, …, c, i ∈ I}`. Lemma 00TE
reads smoothness at a prime off exactly these minors: `R → S` is smooth at `q` if and only if some
`g_I` avoids `q`. The image of `g_I` in `κ(p)[x_1, …, x_n]` is the corresponding minor of the
partial derivatives of the images of the `f_j`, and the presentation reduces to a relative global
complete intersection presentation of the fibre, so Lemma 00TE applied to
`κ(p) → S ⊗_R κ(p)` reads smoothness of the fibre at the prime corresponding to `q` off the very
same minors. Hypothesis (3) is therefore literally the conclusion.

## Main results

* `Algebra.exists_notMem_smooth_of_isSmoothAt_fiber`: flat at `q`, of finite presentation near `q`,
  and with smooth fibre at `q` implies smooth at `q`, 00TF.

## Implementation notes

*This is the full generality of the tag, of which Mathlib's `@[stacks 00TF]`
`Algebra.IsSmoothAt.of_formallySmooth_fiber` is the special case where all three hypotheses are
imposed globally* — `Algebra.FinitePresentation R S` for (1), `Module.Flat R S` for (2), and formal
smoothness of the whole fibre for (3) — as the comment above that declaration records. Each
hypothesis here is the localization of that one at `q`: (1) is the source's `∃ g ∉ q`; (2) follows
from `Module.Flat R S` by `Module.Flat.trans R S (Localization.AtPrime q)`; and (3) is smoothness
of the fibre at one prime rather than at all of them. The specialization is genuine: an algebra
smooth over `R` at one prime and nowhere else satisfies these hypotheses at that prime and none of
the global ones.

*Hypothesis (3) is stated in Mathlib's spelling `Algebra.IsSmoothAt` and the conclusion in the
source's Definition 00TB, `∃ g ∉ q` with `S_g` smooth.* The two notions agree in the presence of
(1) — `Algebra.basicOpen_subset_smoothLocus_iff_smooth` with `Algebra.isOpen_smoothLocus`, applied
inside the finitely presented algebra `S_g`, which is where both notions are computed — so this is
not a mixture of two meanings of "smooth at a prime" but a choice, in each position, of the form
that makes the statement strongest: the weaker hypothesis and the stronger conclusion.
`Algebra.IsSmoothAt R q`, which is formal smoothness of `S_q` and carries no finiteness, is the
weaker of the two: writing it in the conclusion would leave (1) doing nothing but repairing the
meaning of the conclusion, and the same substitution is what makes Lemma 00TC outright
false. Localizations are the concrete `Localization.Away g`, as in Mathlib's
`Algebra.IsSmoothAt.exists_notMem_smooth`, whose conclusion this is; nothing is lost, since
`IsLocalization.algEquiv` transfers smoothness to any other model.

*The fibre is Mathlib's `Ideal.Fiber`, `p.Fiber S = κ(p) ⊗_R S`, and "the prime corresponding to
`q`" is `Ideal.comap` along `Algebra.TensorProduct.includeRight`.* That comap is the inverse of the
bijection `PrimeSpectrum.preimageEquivFiber` between `Spec(κ(p) ⊗_R S)` and the fibre of
`Spec(S) → Spec(R)` over `p`, so `hq` says exactly that `Q` *is* the prime of the fibre
corresponding to `q`, and `Q` is the unique prime of the fibre satisfying it. The fibre is not
abstracted to an `Algebra.IsPushout R S κ(p) F`: it would gain nothing, because the `S`-algebra
structure on `κ(p) ⊗_R S` is `Algebra.TensorProduct.rightAlgebra`, which is deliberately not an
instance, so every instantiation — the standard model included — would have to supply that
structure and the pushout square by hand, while the prime correspondence and the localization of
the fibre (`Ideal.Fiber.localizationAlgEquivQuotient`) are already API of `Ideal.Fiber`.

*Flatness of the local homomorphism `R_p → S_q` is spelled
`Module.Flat R (Localization.AtPrime q)`, flatness over `R` itself.* For an `R_p`-module the two
are the same statement, by
`Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl`, and `S_q` is an
`R_p`-algebra because `q` lies over `p`. Over `R` the hypothesis needs neither the `R_p`-algebra
structure on `S_q` (Mathlib's `Localization.AtPrime.algebraOfLiesOver`, a definition and not an
instance) nor `Localization.AtPrime.IsLiesOverAlgebra`, and it is the pointwise form of the
`Module.Flat R S` in the upstream sibling.

*`q.LiesOver p` is not a hypothesis: it follows from `hq`*, since every prime of `κ(p) ⊗_R S`
lies over `p` and comap along `includeRight` preserves that. So `p` is pinned as the prime `q`
lies over, exactly as in the source, without stating it twice.

Faithfulness. (1) No hypothesis is dead: without (1) the conclusion cannot even hold, as it asserts
finite presentation of some `S_g`; without (2) it fails for `R = ℤ`, `S = 𝔽_2`, `p = q = (2)`,
whose fibre `𝔽_2` is smooth over `κ(p) = 𝔽_2` while `ℤ → 𝔽_2` is smooth at no prime; without (3)
it fails for `R = k`, `S = k[x, y]/(xy)` at `q = (x, y)`, which is flat and of finite presentation
over the field `k`. (2) The scalars and the bases are the source's: (3) is smoothness over the
residue field `κ(p)` of `R` at `p`, not over `R` or over `R_p`, and the conclusion is smoothness of
`S_g` over `R` itself, not over `R_p`; the one deliberate change of base, `R` in place of `R_p` in
(2), is an equality of hypotheses and is recorded above. (3) The canonical maps are pinned rather
than merely asserted to exist: `hq` pins `Q` as the prime of the fibre corresponding to `q` through
`S → κ(p) ⊗_R S`, and the conclusion names the localization `S_g` of `S` at the element `g`, with
its `R`-algebra structure through `R → S`, rather than asserting that some smooth `R`-algebra
localizes `S`. (4) The instantiation is not degenerate: for `R = ℤ`, `S = ℤ[x]`, `p = (2)`,
`q = (2)S` the fibre is `𝔽_2[x]` and `Q = (0)`, all three hypotheses hold with `g = 1`, and the
conclusion holds and is not vacuous; the two failures listed under (1) show that neither the
flatness nor the fibre hypothesis can be dropped, so the statement is not an implication with an
unsatisfiable or an automatic antecedent.

## References

* [Stacks 00TF](https://stacks.math.columbia.edu/tag/00TF), Lemma 10.137.16, in Section 10.137
  "Smooth ring maps". Definition 00TB of smoothness at a prime is spelled out in the conclusion,
  and the source's proof uses Lemma 00SY (flat plus smooth fibre gives a relative global complete
  intersection after localizing), Lemma 00T5 and Lemma 00TE (the Jacobian criterion for smoothness
  of a relative global complete intersection at a prime).

## Tags

smooth ring map, smooth at a prime, fibre, flat, finite presentation
-/

@[expose] public section

/-- **Flat with a smooth fibre implies smooth, at a prime.** Let `R → S` be a ring map, let `q` be
a prime of `S` and let `Q` be the prime of the fibre `κ(p) ⊗_R S` corresponding to `q`, where `p`
is the prime of `R` under `q`. Assume that `R → S_g` is of finite presentation for some `g ∉ q`,
that `S_q` is flat over `R` — equivalently, that the local homomorphism `R_p → S_q` is flat — and
that the fibre is smooth over `κ(p)` at `Q`. Then `R → S` is smooth at `q`: there is a `g ∈ S`,
`g ∉ q`, with `R → S_g` smooth (Definition 00TB).

Note that `q` lies over `p` automatically, this being part of `hq`. -/
@[stacks 00TF "Smoothness at `q` in the conclusion is spelled out as Definition 00TB, `∃ g ∉ q`
with `Localization.Away g` smooth over `R`, while smoothness of the fibre at `Q` is Mathlib's
`Algebra.IsSmoothAt`; the two notions agree under hypothesis (1), so this is the weakest hypothesis
with the strongest conclusion. The fibre is `Ideal.Fiber` and `Q` is pinned as the prime
corresponding to `q` by `hq`, the inverse of `PrimeSpectrum.preimageEquivFiber`. Flatness of
`R_p → S_q` is stated over `R`, which for the `R_p`-algebra `S_q` is the same condition
(`Module.flat_iff_of_isLocalization`). This is the full generality of the tag; upstream's
`Algebra.IsSmoothAt.of_formallySmooth_fiber` is the case of all three hypotheses imposed globally.
See the module docstring.", sga "1 II 2.1" "(a) + (b) ⇒ smooth", sga "3 VIB 3.10" "special case"]
public theorem Algebra.exists_notMem_smooth_of_isSmoothAt_fiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber S)) [Q.IsPrime]
    [Algebra.IsSmoothAt p.ResidueField Q] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    (hq : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) = q)
    (hfp : ∃ g ∉ q, Algebra.FinitePresentation R (Localization.Away g)) :
    ∃ g ∉ q, Algebra.Smooth R (Localization.Away g) :=
  Stacks.Smooth.FlatFibreCriterion.solution p Q q hq hfp

end

/-!
# The locus of smoothness at a prime, and its comparison with the smooth locus

Definition 00TB puts a prime `q ⊂ S` in the smooth locus of `R → S` when some localization `S_g`
with `g ∉ q` is smooth over `R`; Mathlib's `Algebra.smoothLocus R S` instead collects the primes
`q` with `S_q` formally smooth over `R`. The first locus is always open, being a union of standard
opens, and is contained in the second; the two agree as soon as `S` is of finite presentation over
`R`, but not before (`k[x_i : i ∈ ℕ]` over `k` has empty first locus and full second locus).

## Main results

* `Algebra.isOpen_setOf_smoothAt`: the locus of Definition 00TB is open, with no finiteness
  hypothesis.
* `Algebra.isSmoothAt_of_smoothAt`: Definition 00TB smoothness at `q` implies formal smoothness
  of `S_q`.
* `Algebra.smoothAt_iff_isSmoothAt`, `Algebra.setOf_smoothAt_eq_smoothLocus`: the two notions, and
  the two loci, agree for an algebra of finite presentation.

## References

* [Stacks 00TB](https://stacks.math.columbia.edu/tag/00TB), Definition 10.137.11.
-/

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The locus of primes at which `R → S` is smooth in the sense of Definition 00TB is open: it is
the union of the standard opens `D(g)` taken over those `g : S` for which `S_g` is smooth over `R`.

No finiteness hypothesis is needed, in contrast with `Algebra.isOpen_smoothLocus`. -/
theorem isOpen_setOf_smoothAt :
    IsOpen {q : PrimeSpectrum S | Algebra.SmoothAt R S q.asIdeal} := by
  have hunion : {q : PrimeSpectrum S | Algebra.SmoothAt R S q.asIdeal} =
      ⋃ g ∈ {g : S | Algebra.Smooth R (Localization.Away g)},
        (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe,
      PrimeSpectrum.mem_basicOpen, exists_prop]
    exact ⟨fun ⟨g, hgq, hg⟩ => ⟨g, hg, hgq⟩, fun ⟨g, hg, hgq⟩ => ⟨g, hgq, hg⟩⟩
  rw [hunion]
  exact isOpen_biUnion fun g _ => PrimeSpectrum.isOpen_basicOpen

/-- Smoothness at a prime in the sense of Definition 00TB implies Mathlib's `Algebra.IsSmoothAt`,
that is, formal smoothness of the local ring `S_q` over `R`: the local ring of `S` at `q` is also
the local ring of `S_g` at `q S_g`, and `S → S_q` is formally étale.

The converse needs `S` of finite presentation over `R`; see `Algebra.smoothAt_iff_isSmoothAt`. -/
theorem isSmoothAt_of_smoothAt {q : Ideal S} [q.IsPrime] (hq : Algebra.SmoothAt R S q) :
    Algebra.IsSmoothAt R q := by
  obtain ⟨g, hgq, hgs⟩ := hq
  let : Algebra (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers g)
      q.primeCompl (Submonoid.powers_le.mpr hgq)
  let : IsScalarTower S (Localization.Away g) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  let : IsScalarTower R (Localization.Away g) (Localization.AtPrime q) := .to₁₃₄ _ S _ _
  have : IsLocalization (q.primeCompl.map (algebraMap S (Localization.Away g)))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away g)
      (Localization.AtPrime q) (Submonoid.powers g) q.primeCompl
      (Submonoid.powers_le.mpr hgq)
  let : Algebra.FormallySmooth (Localization.Away g) (Localization.AtPrime q) :=
    Algebra.FormallySmooth.of_isLocalization
      (q.primeCompl.map (algebraMap S (Localization.Away g)))
  let : Algebra.FormallySmooth R (Localization.Away g) := hgs.formallySmooth
  exact Algebra.FormallySmooth.comp R (Localization.Away g) (Localization.AtPrime q)

/-- For an algebra of finite presentation, smoothness at a prime in the sense of Definition 00TB
agrees with formal smoothness of the local ring. -/
theorem smoothAt_iff_isSmoothAt [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] :
    Algebra.SmoothAt R S q ↔ Algebra.IsSmoothAt R q := by
  refine ⟨isSmoothAt_of_smoothAt R S, fun h => ?_⟩
  let := h
  exact Algebra.IsSmoothAt.exists_notMem_smooth R q

/-- For an algebra of finite presentation, the locus of Definition 00TB is Mathlib's
`Algebra.smoothLocus`. -/
theorem setOf_smoothAt_eq_smoothLocus [Algebra.FinitePresentation R S] :
    {q : PrimeSpectrum S | Algebra.SmoothAt R S q.asIdeal} = Algebra.smoothLocus R S := by
  ext q
  exact smoothAt_iff_isSmoothAt R S q.asIdeal

end Algebra
