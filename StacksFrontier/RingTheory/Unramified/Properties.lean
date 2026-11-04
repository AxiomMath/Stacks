module


public import StacksFrontier.RingTheory.Unramified.Defs
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Unramified ring maps are those of finite type with vanishing differentials

Proof of `Algebra.unramified_iff_and_gUnramified_iff` (Stacks 00UU): a ring map `R → S` is
unramified if and only if it is of finite type with `Ω_{S/R} = 0`, and G-unramified if and only if
it is of finite presentation with `Ω_{S/R} = 0`.

Both classes are, by definition, formal unramifiedness together with a finiteness condition
(`Algebra.Unramified` for finite type, `Algebra.GUnramified` for finite presentation, Definition
00UT). So each equivalence is the conjunction of the identity on the finiteness conjunct with
Lemma 00UO, `Algebra.formallyUnramified_iff : Algebra.FormallyUnramified R S ↔ Subsingleton
Ω[S⁄R]`, on the other. This is the source's proof — "follows from Lemma 00UO and the definitions"
— and the two directions of that lemma are the two directions of each equivalence.

## Main results

* `Stacks.Unramified.DifferentialCriterion.solution`: the statement of Stacks 00UU, both
  equivalences.

## References

* [Stacks 00UU](https://stacks.math.columbia.edu/tag/00UU), Lemma 10.151.2.
-/

/-!
# Unramified ring maps are those of finite type with vanishing differentials

Let `R → S` be a ring map. The source defines `R → S` to be *unramified* if it is of finite type
and `Ω_{S/R} = 0`, and *G-unramified* if it is of finite presentation and `Ω_{S/R} = 0`
(Definition 00UT). Formal unramifiedness — the uniqueness of a lift along a square-zero
extension — is the same condition as the vanishing of `Ω_{S/R}` (Lemma 00UO,
`Algebra.formallyUnramified_iff`). Hence `R → S` is unramified exactly when it is formally
unramified and of finite type, and G-unramified exactly when it is formally unramified and of
finite presentation. This is the lemma stated here, in the direction that carries its content:
the two classes `Algebra.Unramified` and `Algebra.GUnramified`, which are *defined* by the
formal condition together with the corresponding finiteness condition, are characterised by the
source's conditions, with `Ω_{S/R} = 0` written out.

## Main results

* `Algebra.unramified_iff_and_gUnramified_iff`: `R → S` is unramified if and only if it is of
  finite type with `Ω_{S/R} = 0`, and G-unramified if and only if it is of finite presentation
  with `Ω_{S/R} = 0`.

## Implementation notes

*The module of differentials is written out, and formal unramifiedness is not.* In this library
the source's two definitions are `Algebra.Unramified` (Mathlib's, already tagged 00UT) and
`Algebra.GUnramified`, both of which take the *formal* condition as a field, as Mathlib does for
`Algebra.Smooth` and `Algebra.Etale`. Transcribing the lemma literally — "formally unramified and
of finite type" if and only if "unramified" — would therefore be a statement of structure eta,
true for the trivial reason and asserting nothing about `Ω_{S/R}`. Unfolding the source's
definitions on the right instead puts the whole content of the lemma into the statement: each
equivalence is the source's Definition 00UT paired with Lemma 00UO, whose two directions are the
two directions proved here. `Ω_{S/R} = 0` is `Subsingleton Ω[S⁄R]`, which is Mathlib's spelling in
`Algebra.formallyUnramified_iff`; the conjuncts on the right are in the source's order, finiteness
first.

*The two equivalences are one declaration.* They are one lemma in the source, they have the same
proof, and neither is a special case of the other: they differ in the finiteness condition, which
is not a parameter of anything here. The name is Mathlib's `Algebra.formallyUnramified_iff` with
the two subjects of this lemma in place of its one.

*Stated for an `R`-algebra, not for a bare ring map.* This is how Mathlib states the notions
involved; for `f : R →+* S` the statement is this one at `f.toAlgebra`. No hypothesis is placed on
`R` or `S` beyond commutativity: the equivalences hold with no finiteness, flatness or Noetherian
assumption, and the finiteness conditions appear only where the source puts them, inside the
statement.

Faithfulness to [Stacks 00UU]. (1) No hypothesis is idle: the only hypotheses are the two
commutative ring structures and the algebra structure, which are the ring map of the statement,
and both occur in each side of both equivalences; the finiteness conditions are asserted, not
assumed. (2) The scalars and the base are the source's: finite type, finite presentation and the
Kähler differentials `Ω[S⁄R]` are all taken over `R`, the source of the given map, not over a
localization of `R` and not over `S`. (3) The canonical map is pinned: the instance `Algebra R S`
*is* the map `R → S` of the statement, and `Ω[S⁄R]` is `KaehlerDifferential R S` for that map, so
no differentials of some other algebra structure can satisfy the statement. (4) The
instantiation is not degenerate: for `R → R` both sides of both equivalences hold, and for
`ℚ → ℚ[X]`, which is of finite presentation, both right-hand sides fail because `Ω[ℚ[X]⁄ℚ]` is
free of rank one, so neither equivalence is vacuously true and neither is a statement about an
empty class.

## References

* [Stacks 00UU](https://stacks.math.columbia.edu/tag/00UU), Lemma 10.151.2, in Section 10.151
  "Unramified ring maps" (Section 00US). The definitions of unramified and G-unramified are
  Definition 10.151.1 ([Stacks 00UT]), and the identification of the vanishing of `Ω_{S/R}` with
  formal unramifiedness is Lemma 00UO.
-/

@[expose] public section

/-- **Stacks 00UU.** A ring map `R → S` is unramified if and only if it is of finite type and
`Ω_{S/R} = 0`, and G-unramified if and only if it is of finite presentation and `Ω_{S/R} = 0`.
Both equivalences come from the identification of the vanishing of `Ω_{S/R}` with formal
unramifiedness (Lemma 00UO, `Algebra.formallyUnramified_iff`), which is the condition that
`Algebra.Unramified` and `Algebra.GUnramified` pair with their finiteness conditions. -/
@[stacks 00UU "Both equivalences, as one lemma. `Ω_{S/R} = 0` is written out as
`Subsingleton Ω[S⁄R]` on the right of each; on the left, `Algebra.Unramified` and
`Algebra.GUnramified` (Definition 00UT) are formal unramifiedness together with finite type
resp. finite presentation, so the literal reading of the lemma would be structure eta. See the
module docstring.", ega "IV 17.3.2" "(ii) unramified", ega "IV 17.4.2" "affine case: a) ⇔ c)"]
public theorem Algebra.unramified_iff_and_gUnramified_iff (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] :
    (Algebra.Unramified R S ↔ Algebra.FiniteType R S ∧ Subsingleton Ω[S⁄R]) ∧
      (Algebra.GUnramified R S ↔ Algebra.FinitePresentation R S ∧ Subsingleton Ω[S⁄R]) := by
  refine ⟨⟨fun h => ⟨h.finiteType, (Algebra.formallyUnramified_iff R S).mp h.formallyUnramified⟩,
      fun h => ⟨(Algebra.formallyUnramified_iff R S).mpr h.2, h.1⟩⟩,
    ⟨fun h => ⟨h.finitePresentation, (Algebra.formallyUnramified_iff R S).mp h.formallyUnramified⟩,
      fun h => ⟨(Algebra.formallyUnramified_iff R S).mpr h.2, h.1⟩⟩⟩

end

namespace Stacks.Unramified.DifferentialCriterion

/-- A ring map `R → S` is unramified if and only if it is of finite type and `Ω[S⁄R]` is trivial,
and G-unramified if and only if it is of finite presentation and `Ω[S⁄R]` is trivial. -/
public alias solution := Algebra.unramified_iff_and_gUnramified_iff

end Stacks.Unramified.DifferentialCriterion

/-!
# Properties of unramified and G-unramified ring maps

Proof of `Algebra.unramified_and_gUnramified_properties` (Stacks 00UV), the thirteen permanence
properties of unramified and G-unramified ring maps.

The two notions differ only in the finiteness condition — finite type for unramified, finite
presentation for G-unramified — and in every item the two versions are the same argument run with
`Algebra.FiniteType` in place of `Algebra.FinitePresentation`. The vanishing of the differentials
is `Algebra.FormallyUnramified`, so items (1)–(5) are the corresponding permanence properties of
formal unramifiedness paired with those of the two finiteness conditions, all of them Mathlib's.

Items (6)–(11) are the local theory. The unramified locus of `S` over `R` is the complement of
the support of `Ω[S⁄R]`, so the vanishing of the stalk of the differentials at `q` is exactly
unramifiedness at `q` in Mathlib's sense, and the vanishing of the fibre is the same condition by
Nakayama, the differentials of an algebra of finite type being a finite module. That gives (6) and
(7), and (10) and (11) follow because the unramified locus is a union of basic opens together with
the fact that both finiteness conditions are local on the target.

Items (12) and (13) descend the algebra to a `ℤ`-subalgebra of `R` of finite type. For (12) a
finite presentation of `S` is defined over the `ℤ`-subalgebra generated by the coefficients of its
relations, and enlarging that subalgebra so as to make the model formally unramified is a statement
about the single finite module `Ω[S₀⁄R₀]`: base change of differentials turns the hypothesis into
the vanishing of `R ⊗[R₀] Ω[S₀⁄R₀]`, and each of the finitely many generators already dies over a
subalgebra generated by finitely many elements. Item (13) adds to this the Jacobian criterion: for
`S = R[x_1, …, x_n] ⧸ I` the vanishing of `Ω[S⁄R]` produces for each variable a `g_i ∈ I` with
`∂(g_i - x_i)/∂x_k ∈ I` for all `k`, and the ideal generated by those finitely many polynomials
already cuts out a finitely presented algebra with vanishing differentials surjecting onto `S`.

## Main results

* `Stacks.Unramified.PermanenceProperties.solution`: the statement of Stacks 00UV, as one
  conjunction.

## References

* [Stacks 00UV](https://stacks.math.columbia.edu/tag/00UV), Lemma 10.151.5.
-/

namespace Stacks.Unramified.PermanenceProperties

open Algebra TensorProduct



section Local

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The differentials of `S` over `R` have vanishing stalk at a prime `q` of `S` exactly when
`R → S` is unramified at `q`: the unramified locus is the complement of the support of the
differentials. -/
private theorem isUnramifiedAt_iff_subsingleton_localizedModule (q : Ideal S) [q.IsPrime] :
    Algebra.IsUnramifiedAt R q ↔ Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R]) := by
  rw [← Module.notMem_support_iff (p := (⟨q, ‹_›⟩ : PrimeSpectrum S)), ← Set.mem_compl_iff,
    ← Algebra.unramifiedLocus_eq_compl_support]
  exact Iff.rfl

/-- For an algebra of finite type the fibre of the differentials at a prime `q` vanishes exactly
when their stalk does: `Ω[S⁄R]` is a finite `S`-module, so this is Nakayama's lemma. -/
private theorem subsingleton_localizedModule_iff_subsingleton_fiber [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] :
    Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R]) ↔ Subsingleton (q.Fiber Ω[S⁄R]) := by
  have := KaehlerDifferential.finite R S
  rw [← Module.notMem_support_iff (p := (⟨q, ‹_›⟩ : PrimeSpectrum S)),
    Module.mem_support_iff_nontrivial_residueField_tensorProduct (⟨q, ‹_›⟩ : PrimeSpectrum S),
    not_nontrivial_iff_subsingleton]

/-- **The conclusion shared by items (6)–(9).** Unramifiedness at `q` produces a `g ∉ q` with
`R → S_g` unramified, and G-unramified when `S` is of finite presentation, the localization being
of finite presentation over `S`.

Unramifiedness at `q` is a hypothesis *given* finite type rather than an outright one because in
items (7)–(9) the vanishing of a fibre of the differentials only gives the vanishing of the stalk
once `Ω[S⁄R]` is known to be a finite module. -/
private theorem exists_away_of_isUnramifiedAt (q : Ideal S) [q.IsPrime]
    (hq : Algebra.FiniteType R S → Algebra.IsUnramifiedAt R q) :
    (Algebra.FiniteType R S → ∃ g ∉ q, Algebra.Unramified R (Localization.Away g)) ∧
      (Algebra.FinitePresentation R S → ∃ g ∉ q, Algebra.GUnramified R (Localization.Away g)) := by
  refine ⟨fun h ↦ have := h; have := hq h; Algebra.exists_unramified_of_isUnramifiedAt q,
    fun h ↦ ?_⟩
  have := h
  have hft : Algebra.FiniteType R S := .of_finitePresentation
  have := hq hft
  obtain ⟨g, hgq, hg⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := R) q
  have := hg
  have : Algebra.FinitePresentation S (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  exact ⟨g, hgq, hg, .trans R S (Localization.Away g)⟩

/-- **Formal unramifiedness is local on the target**: if `s ⊆ S` generates the unit ideal and
`R → S_g` is formally unramified for every `g ∈ s`, then so is `R → S`. -/
private theorem formallyUnramified_of_span_eq_top {s : Set S} (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Algebra.FormallyUnramified R (Localization.Away g)) :
    Algebra.FormallyUnramified R S := by
  rw [Algebra.formallyUnramified_iff_forall]
  intro q
  obtain ⟨g, hgs, hgq⟩ : ∃ g ∈ s, g ∉ q.asIdeal := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact q.isPrime.ne_top (top_le_iff.mp (hs.ge.trans (Ideal.span_le.mpr h)))
  exact Algebra.basicOpen_subset_unramifiedLocus_iff.mpr (H g hgs) hgq

end Local

section Span

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- **Being unramified is local on the target** (Stacks 00UV (10), the `unramified` version). -/
private theorem unramified_of_span_eq_top {s : Set S} (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Algebra.Unramified R (Localization.Away g)) : Algebra.Unramified R S where
  formallyUnramified :=
    formallyUnramified_of_span_eq_top hs fun g hg ↦ (H g hg).formallyUnramified
  finiteType := Algebra.FiniteType.of_span_eq_top_target s hs fun g hg ↦ (H g hg).finiteType

/-- **Being G-unramified is local on the target** (Stacks 00UV (10), the `G-unramified`
version). -/
private theorem gUnramified_of_span_eq_top {s : Set S} (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Algebra.GUnramified R (Localization.Away g)) : Algebra.GUnramified R S where
  formallyUnramified :=
    formallyUnramified_of_span_eq_top hs fun g hg ↦ (H g hg).formallyUnramified
  finitePresentation :=
    Algebra.FinitePresentation.of_span_eq_top_target s hs fun g hg ↦ (H g hg).finitePresentation

/-- **A property met outside every prime generates the unit ideal**: this turns the pointwise
hypothesis of item (11) into the covering hypothesis of item (10). -/
private theorem span_setOf_eq_top {P : S → Prop} (H : ∀ q : Ideal S, q.IsPrime → ∃ g ∉ q, P g) :
    Ideal.span {g | P g} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hgm, hg⟩ := H m hm.isPrime
  exact hgm (hle (Ideal.subset_span hg))

end Span

section Fibre

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The fibre of a module at a prime is detected after base change.** If `T` is an `S`-algebra,
`q` a prime of `T` and `q'` the prime of `S` under it, then the fibre of `T ⊗[S] M` at `q` is
`κ(q) ⊗_{κ(q')} (κ(q') ⊗_S M)`, and `κ(q)` is a field extension of `κ(q')`, hence faithfully flat;
so the fibre of `M` at `q'` vanishes as soon as that of `T ⊗[S] M` at `q` does. -/
private theorem subsingleton_fiber_comap_of_subsingleton_fiber_baseChange
    {S T : Type*} [CommRing S] [CommRing T] [Algebra S T]
    (M : Type*) [AddCommGroup M] [Module S M] (q : Ideal T) [q.IsPrime]
    (h : Subsingleton (q.Fiber (T ⊗[S] M))) :
    Subsingleton ((q.comap (algebraMap S T)).Fiber M) := by
  set q' := q.comap (algebraMap S T) with hq'
  have : q'.IsPrime := hq' ▸ Ideal.comap_isPrime _ _
  let alg : Algebra q'.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map q' q (algebraMap S T) hq').toAlgebra
  have tower : IsScalarTower S q'.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun s ↦
      (Ideal.ResidueField.map_algebraMap q' q (algebraMap S T) hq' s).symm
  have e₁ : q.Fiber (T ⊗[S] M) ≃ₗ[q.ResidueField] q.ResidueField ⊗[S] M :=
    AlgebraTensorModule.cancelBaseChange S T q.ResidueField q.ResidueField M
  have e₂ : q.ResidueField ⊗[q'.ResidueField] q'.Fiber M ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[S] M :=
    AlgebraTensorModule.cancelBaseChange S q'.ResidueField q.ResidueField q.ResidueField M
  have : Subsingleton (q.ResidueField ⊗[S] M) := e₁.toEquiv.symm.subsingleton
  have : Subsingleton (q.ResidueField ⊗[q'.ResidueField] q'.Fiber M) := e₂.toEquiv.subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality
    (R := q'.ResidueField) (M := q.ResidueField) (q'.Fiber M)

/-- **Items (8) and (9).** If `q` is a prime of the fibre `κ(𝔭) ⊗_R S` and the fibre at `q` of
`Ω[κ(𝔭) ⊗_R S⁄κ(𝔭)]` vanishes, then `R → S` is unramified at the prime of `S` under `q`.

This is the source's argument: the base change identity
`Ω[κ(𝔭) ⊗_R S⁄κ(𝔭)] = (κ(𝔭) ⊗_R S) ⊗_S Ω[S⁄R]`
(`KaehlerDifferential.tensorKaehlerEquiv`, for the pushout square `R → κ(𝔭)`,
`S → κ(𝔭) ⊗_R S`) identifies the two `κ(q)`-vector spaces of items (7) and (9) up to the field
extension `κ(q)/κ(q ∩ S)`, which is faithfully flat. -/
private theorem isUnramifiedAt_comap_includeRight_of_subsingleton_fiber {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : Subsingleton (q.Fiber Ω[p.Fiber S⁄p.ResidueField])) :
    Algebra.IsUnramifiedAt R
      (q.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)).toRingHom) := by
  have h₀ : algebraMap S (p.Fiber S) =
      (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)).toRingHom := rfl
  have e : p.Fiber S ⊗[S] Ω[S⁄R] ≃ₗ[p.Fiber S] Ω[p.Fiber S⁄p.ResidueField] :=
    KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField S (p.Fiber S)
  have e' : q.Fiber Ω[p.Fiber S⁄p.ResidueField] ≃ₗ[p.Fiber S]
      q.Fiber (p.Fiber S ⊗[S] Ω[S⁄R]) :=
    TensorProduct.congr (LinearEquiv.refl (p.Fiber S) q.ResidueField) e.symm
  have h : Subsingleton (q.Fiber (p.Fiber S ⊗[S] Ω[S⁄R])) := e'.toEquiv.symm.subsingleton
  refine (isUnramifiedAt_iff_subsingleton_localizedModule _).mpr
    ((subsingleton_localizedModule_iff_subsingleton_fiber _).mpr ?_)
  exact h₀ ▸ subsingleton_fiber_comap_of_subsingleton_fiber_baseChange Ω[S⁄R] q h

end Fibre

section Descent

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R₀ : Type*} [CommRing R₀] {R : Type*} [CommRing R] [Algebra R₀ R]
  {N : Type*} [AddCommGroup N] [Module R₀ N]

/-- Vanishing of `1 ⊗ n` is inherited by a larger subalgebra of scalars. -/
private theorem one_tmul_eq_zero_of_le {n : N} {B B' : Subalgebra R₀ R} (hB : B ≤ B')
    (h : (1 : B) ⊗ₜ[R₀] n = 0) : (1 : B') ⊗ₜ[R₀] n = 0 := by
  simpa using congrArg (LinearMap.rTensor N (Subalgebra.inclusion hB).toLinearMap) h

/-- **Vanishing in a tensor product is witnessed by finitely many scalars.** If `1 ⊗ n` vanishes
in `R ⊗[R₀] N` then it already vanishes over the `R₀`-subalgebra of `R` generated by a finite
set. -/
private theorem exists_finset_one_tmul_eq_zero {n : N} (h : (1 : R) ⊗ₜ[R₀] n = 0) :
    ∃ s : Finset R, (1 : Algebra.adjoin R₀ (s : Set R)) ⊗ₜ[R₀] n = 0 := by
  classical
  set P : Submodule R₀ R := Submodule.span R₀ {1}
  have h1 : (1 : R) ∈ P := Submodule.mem_span_singleton_self 1
  have ht : LinearMap.rTensor N P.subtype ((⟨1, h1⟩ : P) ⊗ₜ[R₀] n) = 0 := by simpa using h
  obtain ⟨Q, hPQ, hQ, hQ0⟩ :=
    TensorProduct.eq_zero_of_fg_of_subtype_eq_zero (Submodule.fg_span_singleton 1) ht
  obtain ⟨s, hs⟩ := hQ
  refine ⟨s, ?_⟩
  have hle : Q ≤ Subalgebra.toSubmodule (Algebra.adjoin R₀ (s : Set R)) := by
    rw [← hs, Submodule.span_le]
    exact fun x hx ↦ Algebra.subset_adjoin hx
  have h2 := congrArg (LinearMap.rTensor N (Submodule.inclusion hle)) hQ0
  simp only [map_zero, LinearMap.rTensor_tmul] at h2
  exact h2

/-- **A tensor product dies once a generating set of the right factor does.** If `N` is generated
over an `R₀`-algebra `S₀` by a set `t` and `1 ⊗ n` vanishes in `B ⊗[R₀] N` for every `n ∈ t`, then
`B ⊗[R₀] N` vanishes.

The set of `n` with `1 ⊗ n = 0` is an `S₀`-submodule of `N` although `B ⊗[R₀] N` need carry no
`S₀`-action: multiplication by `c : S₀` on `N` is `R₀`-linear, so it acts on the tensor product. -/
private theorem subsingleton_tensor_of_span_eq_top {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀]
    [Module S₀ N] [IsScalarTower R₀ S₀ N] {B : Type*} [CommRing B] [Algebra R₀ B] {t : Set N}
    (ht : Submodule.span S₀ t = ⊤) (h : ∀ n ∈ t, (1 : B) ⊗ₜ[R₀] n = 0) :
    Subsingleton (B ⊗[R₀] N) := by
  have key : ∀ n : N, (1 : B) ⊗ₜ[R₀] n = 0 := by
    let K : Submodule S₀ N :=
      { carrier := {n | (1 : B) ⊗ₜ[R₀] n = 0}
        add_mem' := fun {a b} ha hb ↦ by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [TensorProduct.tmul_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c n hn ↦ by
          simp only [Set.mem_ofPred_eq] at hn ⊢
          simpa using congrArg
            (LinearMap.lTensor B ((LinearMap.lsmul S₀ N c).restrictScalars R₀)) hn }
    have hK : K = ⊤ := by
      rw [_root_.eq_top_iff, ← ht, Submodule.span_le]
      exact fun n hn ↦ h n hn
    exact fun n ↦ (hK.ge Submodule.mem_top : n ∈ K)
  refine subsingleton_of_forall_eq 0 fun z ↦ ?_
  induction z with
  | zero => rfl
  | tmul b n =>
      rw [show b ⊗ₜ[R₀] n = b • ((1 : B) ⊗ₜ[R₀] n) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], key n, smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- **Enlarging the ring of scalars kills a finite module.** If `N` is a finite module over an
`R₀`-algebra `S₀` and `R ⊗[R₀] N` vanishes, then `B ⊗[R₀] N` already vanishes for some
`R₀`-subalgebra `B` of `R` of finite type. -/
private theorem exists_fg_subsingleton_tensor {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀]
    [Module S₀ N] [IsScalarTower R₀ S₀ N] [Module.Finite S₀ N]
    (h : Subsingleton (R ⊗[R₀] N)) :
    ∃ B : Subalgebra R₀ R, B.FG ∧ Subsingleton (B ⊗[R₀] N) := by
  classical
  obtain ⟨t, ht⟩ := Module.finite_def.mp ‹Module.Finite S₀ N›
  choose s hs using fun n : N ↦
    exists_finset_one_tmul_eq_zero (Subsingleton.elim ((1 : R) ⊗ₜ[R₀] n) 0)
  exact ⟨Algebra.adjoin R₀ ((t.biUnion s : Finset R) : Set R), ⟨t.biUnion s, rfl⟩,
    subsingleton_tensor_of_span_eq_top ht fun n hn ↦ one_tmul_eq_zero_of_le
      (Algebra.adjoin_mono (by exact_mod_cast Finset.subset_biUnion_of_mem s hn)) (hs n)⟩

/-- **Base change of differentials.** The differentials of `R ⊗[R₀] S₀` over `R` are the base
change of the differentials of `S₀` over `R₀`; in particular one vanishes exactly when the other
does. -/
private theorem subsingleton_kaehlerDifferential_tensor_iff (R₀ R S₀ : Type*) [CommRing R₀]
    [CommRing R] [CommRing S₀] [Algebra R₀ R] [Algebra R₀ S₀] :
    Subsingleton Ω[(R ⊗[R₀] S₀)⁄R] ↔ Subsingleton (R ⊗[R₀] Ω[S₀⁄R₀]) :=
  have e₁ : (R ⊗[R₀] S₀) ⊗[S₀] Ω[S₀⁄R₀] ≃ₗ[R ⊗[R₀] S₀] Ω[(R ⊗[R₀] S₀)⁄R] :=
    KaehlerDifferential.tensorKaehlerEquiv R₀ R S₀ (R ⊗[R₀] S₀)
  have e₂ : (R ⊗[R₀] S₀) ⊗[S₀] Ω[S₀⁄R₀] ≃ₗ[R] R ⊗[R₀] Ω[S₀⁄R₀] :=
    Algebra.IsPushout.cancelBaseChange R₀ R S₀ (R ⊗[R₀] S₀) Ω[S₀⁄R₀]
  (e₁.toEquiv.symm.trans e₂.toEquiv).subsingleton_congr

/-- **Item (12).** A G-unramified algebra is a base change of a G-unramified algebra over a
`ℤ`-subalgebra of the base of finite type.

Mathlib's `Algebra.Presentation.Core` supplies the `ℤ`-subalgebra `R₀` generated by the
coefficients of the relations of a finite presentation of `S`, a model `S₀` of finite presentation
over `R₀`, and the isomorphism `S ≃ₐ[R] R ⊗[R₀] S₀`. What is left is to enlarge `R₀` so that the
model becomes formally unramified. That is a statement about one finite module rather than about
polynomials: with `N = Ω[S₀⁄R₀]`, base change of differentials turns the hypothesis into
`R ⊗[R₀] N = 0`, and each of the finitely many generators of `N` already dies over a subalgebra
of `R` generated by finitely many elements. -/
private theorem exists_finiteType_int_baseChange_of_gUnramified {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (h : Algebra.GUnramified R S) :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      Algebra.FiniteType ℤ R₀ ∧ Algebra.GUnramified R₀ S₀ ∧
        Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  have := h
  have := h.finitePresentation
  set P := Algebra.Presentation.ofFinitePresentation R S
  set A := P.Core
  set S₀ := P.ModelOfHasCoeffs A
  have e : R ⊗[A] S₀ ≃ₐ[R] S := P.tensorModelOfHasCoeffsEquiv A
  have h1 : Subsingleton Ω[(R ⊗[A] S₀)⁄R] :=
    ((Algebra.FormallyUnramified.iff_of_equiv e).mpr
      inferInstance).subsingleton_kaehlerDifferential
  have h2 : Subsingleton (R ⊗[A] Ω[S₀⁄A]) :=
    (subsingleton_kaehlerDifferential_tensor_iff A R S₀).mp h1
  have : Module.Finite S₀ Ω[S₀⁄A] := KaehlerDifferential.finite A S₀
  obtain ⟨B, hBfg, hB⟩ := exists_fg_subsingleton_tensor (S₀ := S₀) h2
  have hBft : Algebra.FiniteType A B := ⟨B.fg_top.mpr hBfg⟩
  refine ⟨B.toSubring, ↥B ⊗[A] S₀, inferInstance, inferInstance, ?_, ⟨⟨?_⟩, ?_⟩, ⟨?_⟩⟩
  · exact Algebra.FiniteType.trans (R := ℤ) (S := A) (A := ↥B) inferInstance hBft
  · exact (subsingleton_kaehlerDifferential_tensor_iff A (↥B) S₀).mpr hB
  · exact inferInstanceAs (Algebra.FinitePresentation (↥B) (↥B ⊗[A] S₀))
  · exact e.symm.trans (Algebra.TensorProduct.cancelBaseChange A (↥B) R R S₀).symm

end Descent

section Jacobian

/-- **The differentials of a quotient vanish exactly when the cotangent map is onto.** For a
surjection `A → B` of `R`-algebras the sequence `I/I² → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → 0` is exact, so
`Ω[B⁄R]` vanishes if and only if the first map already hits everything. -/
private theorem subsingleton_kaehlerDifferential_iff_range_kerCotangentToTensor_eq_top
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] (h : Function.Surjective (algebraMap A B)) :
    Subsingleton Ω[B⁄R] ↔
      LinearMap.range (KaehlerDifferential.kerCotangentToTensor R A B) = ⊤ := by
  rw [KaehlerDifferential.range_kerCotangentToTensor R A B h,
    Submodule.restrictScalars_eq_top_iff, LinearMap.ker_eq_top]
  refine ⟨fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _, fun h0 ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain ⟨x', rfl⟩ := KaehlerDifferential.mapBaseChange_surjective R A B h x
  obtain ⟨y', rfl⟩ := KaehlerDifferential.mapBaseChange_surjective R A B h y
  rw [h0]
  rfl

/-- The `d x_k` span the base change of the differentials of a polynomial ring to a quotient `B` of
it — and span it already over the polynomial ring, the map to `B` being onto. -/
private theorem span_one_tmul_D_X_eq_top (R : Type*) [CommRing R] (σ : Type*) (B : Type*)
    [CommRing B] [Algebra (MvPolynomial σ R) B]
    (h : Function.Surjective (algebraMap (MvPolynomial σ R) B)) :
    Submodule.span (MvPolynomial σ R) (Set.range fun i : σ ↦ (1 : B) ⊗ₜ[MvPolynomial σ R]
      KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) = ⊤ := by
  have hb : ∀ i : σ, ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange B) i =
      (1 : B) ⊗ₜ[MvPolynomial σ R]
        KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i) := by
    simp [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  rw [← Submodule.restrictScalars_span _ B h, ← funext hb,
    ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange B).span_eq,
    Submodule.restrictScalars_top]

/-- The `k`-th coordinate of `1 ⊗ d f`, in the base change to `R[σ] ⧸ I` of the standard basis
`(d x_k)` of the differentials of a polynomial ring, is the partial derivative `∂f/∂x_k` read in
the quotient. -/
@[ega "IV 16.5.8" "special case"]
private theorem mvPolynomialBasis_baseChange_repr_one_tmul_D {R : Type*} [CommRing R] {σ : Type*}
    (I : Ideal (MvPolynomial σ R)) (f : MvPolynomial σ R) (k : σ) :
    (((KaehlerDifferential.mvPolynomialBasis R σ).baseChange (MvPolynomial σ R ⧸ I)).repr
        (1 ⊗ₜ[MvPolynomial σ R] KaehlerDifferential.D R (MvPolynomial σ R) f)) k =
      Ideal.Quotient.mk I (MvPolynomial.pderiv k f) := by
  rw [Module.Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]

/-- **The Jacobian criterion, one polynomial at a time.** For `A = R[σ]` and an ideal `I` of `A`,
the element `1 ⊗ d f` of `(A ⧸ I) ⊗[A] Ω[A⁄R]` vanishes exactly when every partial derivative of
`f` lies in `I`, because `Ω[A⁄R]` is free on the `d x_k`. -/
private theorem one_tmul_D_eq_zero_iff_pderiv_mem {R : Type*} [CommRing R] {σ : Type*}
    (I : Ideal (MvPolynomial σ R)) (f : MvPolynomial σ R) :
    (1 : MvPolynomial σ R ⧸ I) ⊗ₜ[MvPolynomial σ R]
        KaehlerDifferential.D R (MvPolynomial σ R) f = 0 ↔
      ∀ k, MvPolynomial.pderiv k f ∈ I := by
  rw [← ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange
    (MvPolynomial σ R ⧸ I)).repr.map_eq_zero_iff]
  constructor
  · intro h k
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← mvPolynomialBasis_baseChange_repr_one_tmul_D I f k, h, Finsupp.coe_zero, Pi.zero_apply]
  · intro h
    ext k
    rw [mvPolynomialBasis_baseChange_repr_one_tmul_D I f k, Finsupp.coe_zero, Pi.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact h k

/-- **Vanishing differentials produce the relations of the Jacobian criterion.** If `Ω[(A ⧸ I)⁄R]`
vanishes then every `a : A` differs, modulo `I` and up to first order, from an element of `I`:
there is a `g ∈ I` with `1 ⊗ d(g - a) = 0` in `(A ⧸ I) ⊗[A] Ω[A⁄R]`. -/
private theorem exists_mem_one_tmul_D_sub_eq_zero {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal A) (h : Subsingleton Ω[(A ⧸ I)⁄R]) (a : A) :
    ∃ g ∈ I, (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D R A (g - a) = 0 := by
  have hker : RingHom.ker (algebraMap A (A ⧸ I)) = I := by simp [Ideal.Quotient.algebraMap_eq]
  obtain ⟨ξ, hξ⟩ : (1 : A ⧸ I) ⊗ₜ[A] KaehlerDifferential.D R A a ∈
      LinearMap.range (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I)) :=
    (subsingleton_kaehlerDifferential_iff_range_kerCotangentToTensor_eq_top R A (A ⧸ I)
      Ideal.Quotient.mk_surjective).mp h ▸ Submodule.mem_top
  obtain ⟨⟨g, hg⟩, rfl⟩ := Ideal.toCotangent_surjective _ ξ
  refine ⟨g, hker ▸ hg, ?_⟩
  rw [map_sub, TensorProduct.tmul_sub, sub_eq_zero, ← hξ,
    KaehlerDifferential.kerCotangentToTensor_toCotangent]

/-- **The Jacobian criterion for vanishing differentials.** If an ideal `J` of `R[σ]` contains, for
every variable `x_i`, an element `g_i` together with all the partial derivatives of `g_i - x_i`,
then `Ω[(R[σ] ⧸ J)⁄R]` vanishes: the class of `g_i` in `J/J²` maps to `1 ⊗ d(g_i)`, which by the
Jacobian criterion equals `1 ⊗ d x_i`, and the `1 ⊗ d x_i` span the base change of `Ω[R[σ]⁄R]`. -/
private theorem subsingleton_kaehlerDifferential_quotient_of_forall_pderiv_mem {R : Type*}
    [CommRing R] {σ : Type*} (J : Ideal (MvPolynomial σ R)) (g : σ → MvPolynomial σ R)
    (hgJ : ∀ i, g i ∈ J)
    (hpd : ∀ i k, MvPolynomial.pderiv k (g i - MvPolynomial.X i) ∈ J) :
    Subsingleton Ω[(MvPolynomial σ R ⧸ J)⁄R] := by
  refine (subsingleton_kaehlerDifferential_iff_range_kerCotangentToTensor_eq_top R
    (MvPolynomial σ R) _ Ideal.Quotient.mk_surjective).mpr ?_
  rw [← top_le_iff, ← span_one_tmul_D_X_eq_top R σ (MvPolynomial σ R ⧸ J)
    Ideal.Quotient.mk_surjective, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h0 := (one_tmul_D_eq_zero_iff_pderiv_mem J (g i - MvPolynomial.X i)).mpr (hpd i)
  rw [map_sub, TensorProduct.tmul_sub, sub_eq_zero] at h0
  refine ⟨Ideal.toCotangent _ ⟨g i, ?_⟩, ?_⟩
  · simpa [Ideal.Quotient.algebraMap_eq, RingHom.mem_ker] using hgJ i
  · rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent]

/-- **An unramified algebra is a quotient of a G-unramified one.** This is the only step of item
(13) that goes beyond item (12), and it is where the source's Jacobian identity is used.

Write `S = A ⧸ I` with `A = R[x_1, …, x_n]`. Vanishing of `Ω[S⁄R]` gives for every `i` an element
`g_i ∈ I` with `1 ⊗ d(g_i - x_i) = 0` in `S ⊗[A] Ω[A⁄R]`, that is, with all partial derivatives of
`g_i - x_i` in `I`. Quotienting `A` by the ideal `J` generated by the `g_i` together with those
finitely many partial derivatives gives a finitely presented `R`-algebra which still surjects onto
`S`, and whose differentials vanish by the Jacobian criterion. -/
private theorem exists_gUnramified_surjective_of_unramified {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (h : Algebra.Unramified R S) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (f : S' →ₐ[R] S),
      Algebra.GUnramified R S' ∧ Function.Surjective f := by
  classical
  have := h
  have := h.finiteType
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ‹Algebra.FiniteType R S›
  set A := MvPolynomial (Fin n) R
  set I : Ideal A := RingHom.ker φ.toRingHom
  have hsub : Subsingleton Ω[(A ⧸ I)⁄R] :=
    ((Algebra.FormallyUnramified.iff_of_equiv
      (Ideal.quotientKerAlgEquivOfSurjective hφ)).mpr
        inferInstance).subsingleton_kaehlerDifferential
  choose g hgI hgD using fun i : Fin n ↦
    exists_mem_one_tmul_D_sub_eq_zero I hsub (MvPolynomial.X i)
  set J : Ideal A := Ideal.span (Set.range g ∪ Set.range fun p : Fin n × Fin n ↦
    MvPolynomial.pderiv p.2 (g p.1 - MvPolynomial.X p.1)) with hJ
  have hgJ : ∀ i, g i ∈ J := fun i ↦ Ideal.subset_span (.inl ⟨i, rfl⟩)
  have hpdJ : ∀ i k, MvPolynomial.pderiv k (g i - MvPolynomial.X i) ∈ J :=
    fun i k ↦ Ideal.subset_span (.inr ⟨(i, k), rfl⟩)
  have hJI : J ≤ I := by
    rw [hJ, Ideal.span_le]
    rintro x (⟨i, rfl⟩ | ⟨p, rfl⟩)
    · exact hgI i
    · exact (one_tmul_D_eq_zero_iff_pderiv_mem I _).mp (hgD p.1) p.2
  have hJfg : J.FG :=
    Submodule.fg_span (Set.Finite.union (Set.finite_range g) (Set.finite_range _))
  refine ⟨A ⧸ J, inferInstance, inferInstance,
    Ideal.Quotient.liftₐ J φ (fun a ha ↦ hJI ha),
    ⟨⟨subsingleton_kaehlerDifferential_quotient_of_forall_pderiv_mem J g hgJ hpdJ⟩,
      Algebra.FinitePresentation.quotient hJfg⟩, fun x ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hφ x
  exact ⟨Ideal.Quotient.mk J y, rfl⟩

/-- **Item (13).** An unramified algebra is a quotient of a base change of an unramified algebra
over a `ℤ`-subalgebra of the base of finite type: combine
`exists_gUnramified_surjective_of_unramified` with item (12). -/
private theorem exists_finiteType_int_surjective_of_unramified {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] (h : Algebra.Unramified R S) :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
      (f : (R ⊗[R₀] S₀) →ₐ[R] S),
      Algebra.FiniteType ℤ R₀ ∧ Algebra.Unramified R₀ S₀ ∧ Function.Surjective f := by
  obtain ⟨S', _, _, f, hS', hfs⟩ := exists_gUnramified_surjective_of_unramified h
  obtain ⟨R₀, S₀, _, _, hft, hgu, ⟨e⟩⟩ := exists_finiteType_int_baseChange_of_gUnramified hS'
  have := hgu.finitePresentation
  refine ⟨R₀, S₀, inferInstance, inferInstance, f.comp e.symm.toAlgHom, hft,
    ⟨hgu.formallyUnramified, Algebra.FiniteType.of_finitePresentation⟩, ?_⟩
  exact hfs.comp e.symm.surjective

end Jacobian

/-- The statement of Stacks 00UV. -/
public theorem solution :
    -- (1) base change
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (R' : Type w)
        [CommRing R'] [Algebra R R'], (Unramified R S → Unramified R' (R' ⊗[R] S)) ∧
          (GUnramified R S → GUnramified R' (R' ⊗[R] S))) ∧
    -- (2) composition
    (∀ {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
        [Algebra S T] [Algebra R T] [IsScalarTower R S T],
        (Unramified R S → Unramified S T → Unramified R T) ∧
          (GUnramified R S → GUnramified S T → GUnramified R T)) ∧
    -- (3) a principal localization
    (∀ {R : Type u} [CommRing R] (f : R) (Rf : Type v) [CommRing Rf] [Algebra R Rf]
        [IsLocalization.Away f Rf], GUnramified R Rf ∧ Unramified R Rf) ∧
    -- (4) a quotient
    (∀ {R : Type u} [CommRing R] (I : Ideal R),
        Unramified R (R ⧸ I) ∧ (I.FG → GUnramified R (R ⧸ I))) ∧
    -- (5) an étale map
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Etale R S],
        GUnramified R S ∧ Unramified R S) ∧
    -- (6) the stalk of the differentials at the prime vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime],
        Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R]) →
          (FiniteType R S → ∃ g ∉ q, Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g ∉ q, GUnramified R (Localization.Away g))) ∧
    -- (7) the fibre of the differentials at the prime vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime],
        Subsingleton (q.Fiber Ω[S⁄R]) →
          (FiniteType R S → ∃ g ∉ q, Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g ∉ q, GUnramified R (Localization.Away g))) ∧
    -- (8) the stalk of the differentials of the fibre over `𝔭` vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (q : Ideal (p.Fiber S)) [q.IsPrime],
        Subsingleton (LocalizedModule q.primeCompl Ω[p.Fiber S⁄p.ResidueField]) →
          (FiniteType R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                GUnramified R (Localization.Away g))) ∧
    -- (9) the fibre at `q` of the differentials of the fibre over `𝔭` vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (q : Ideal (p.Fiber S)) [q.IsPrime],
        Subsingleton (q.Fiber Ω[p.Fiber S⁄p.ResidueField]) →
          (FiniteType R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                GUnramified R (Localization.Away g))) ∧
    -- (10) descent along a cover of `Spec S` by principal opens
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (s : Set S),
        Ideal.span s = ⊤ →
        ((∀ g ∈ s, Unramified R (Localization.Away g)) → Unramified R S) ∧
          ((∀ g ∈ s, GUnramified R (Localization.Away g)) → GUnramified R S)) ∧
    -- (11) unramified at every prime
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S],
        ((∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, Unramified R (Localization.Away g)) →
            Unramified R S) ∧
          ((∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, GUnramified R (Localization.Away g)) →
            GUnramified R S)) ∧
    -- (12) a G-unramified map is a base change of one over a finite type `ℤ`-algebra
    (∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S], GUnramified R S →
        ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
          FiniteType ℤ R₀ ∧ GUnramified R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀)) ∧
    -- (13) an unramified map is a quotient of a base change of one over a finite type `ℤ`-algebra
    (∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S], Unramified R S →
        ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
          (f : (R ⊗[R₀] S₀) →ₐ[R] S),
          FiniteType ℤ R₀ ∧ Unramified R₀ S₀ ∧ Function.Surjective f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) base change
  · exact fun R' ↦ ⟨fun h ↦ have := h; inferInstance,
      fun h ↦ have := h; ⟨FormallyUnramified.base_change R', FinitePresentation.baseChange R'⟩⟩
  -- (2) composition
  · intro R S T _ _ _ _ _ _ _
    exact ⟨fun h h' ↦ have := h; have := h'; .comp R S T,
      fun h h' ↦ have := h; have := h';
        ⟨FormallyUnramified.comp R S T, FinitePresentation.trans R S T⟩⟩
  -- (3) a principal localization
  · intro R _ f Rf _ _ _
    have : FinitePresentation R Rf := IsLocalization.Away.finitePresentation f
    exact ⟨⟨FormallyUnramified.of_isLocalization (Submonoid.powers f), inferInstance⟩,
      .of_isLocalization_Away f⟩
  -- (4) a quotient
  · exact fun I ↦ ⟨⟨FormallyUnramified.quotient I, inferInstance⟩,
      fun hI ↦ ⟨FormallyUnramified.quotient I, FinitePresentation.quotient hI⟩⟩
  -- (5) an étale map
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  -- (6) the stalk of the differentials at the prime vanishes
  · intro R S _ _ _ q _ hq
    exact exists_away_of_isUnramifiedAt q fun _ ↦
      (isUnramifiedAt_iff_subsingleton_localizedModule q).mpr hq
  -- (7) the fibre of the differentials at the prime vanishes
  · intro R S _ _ _ q _ hq
    exact exists_away_of_isUnramifiedAt q fun hft ↦
      have := hft
      (isUnramifiedAt_iff_subsingleton_localizedModule q).mpr
        ((subsingleton_localizedModule_iff_subsingleton_fiber q).mpr hq)
  -- (8) the stalk of the differentials of the fibre over `p` vanishes
  · intro R S _ _ _ p _ q _ hq
    exact exists_away_of_isUnramifiedAt _ fun hft ↦
      have := hft
      isUnramifiedAt_comap_includeRight_of_subsingleton_fiber p q
        ((subsingleton_localizedModule_iff_subsingleton_fiber q).mp hq)
  -- (9) the fibre at `q` of the differentials of the fibre over `p` vanishes
  · intro R S _ _ _ p _ q _ hq
    exact exists_away_of_isUnramifiedAt _ fun hft ↦
      have := hft
      isUnramifiedAt_comap_includeRight_of_subsingleton_fiber p q hq
  -- (10) descent along a cover of `Spec S` by principal opens
  · exact fun s hs ↦ ⟨unramified_of_span_eq_top hs, gUnramified_of_span_eq_top hs⟩
  -- (11) unramified at every prime
  · intro R S _ _ _
    exact ⟨fun H ↦ unramified_of_span_eq_top
        (s := {g | Unramified R (Localization.Away g)})
        (span_setOf_eq_top fun q hq ↦ have := hq; H q) fun g hg ↦ hg,
      fun H ↦ gUnramified_of_span_eq_top
        (s := {g | GUnramified R (Localization.Away g)})
        (span_setOf_eq_top fun q hq ↦ have := hq; H q) fun g hg ↦ hg⟩
  -- (12) a G-unramified map is a base change of one over a finite type `Z`-algebra
  · exact exists_finiteType_int_baseChange_of_gUnramified
  -- (13) an unramified map is a quotient of a base change of one over a finite type `Z`-algebra
  · exact exists_finiteType_int_surjective_of_unramified

end Stacks.Unramified.PermanenceProperties

/-!
# Properties of unramified and G-unramified ring maps

A ring map `R → S` is *unramified* if it is of finite type with `Ω_{S/R} = 0` and *G-unramified*
if it is of finite presentation with `Ω_{S/R} = 0` (Definition 00UT); it is unramified
(resp. G-unramified) *at a prime* `q` of `S` if `R → S_g` is unramified (resp. G-unramified) for
some `g ∈ S`, `g ∉ q`. This file collects the basic permanence properties of the two notions: both
are stable under base change and composition, both hold for a principal localization and for an
étale map, a quotient map is unramified and is G-unramified when the ideal is finitely generated,
both are local on `S` — detected on a cover of `Spec S` by principal opens, hence at all primes —
both are detected at a prime by the vanishing of a single stalk or fibre of the differentials, and
both descend to a finite type `ℤ`-algebra.

The two notions differ only in the finiteness condition, so each item has a version for each, and
the two versions are proved by the same argument applied to `Algebra.FiniteType` resp.
`Algebra.FinitePresentation`.

## Main results

* `Algebra.unramified_and_gUnramified_properties`: the thirteen items of Lemma 00UV, in the
  source's order, as a conjunction.

Each version of each item is also available under its own name, and it is these that a proof
should cite:

* `Algebra.GUnramified.baseChange`: item (1);
* `Algebra.GUnramified.comp`: item (2);
* `Algebra.GUnramified.of_isLocalization_Away`: item (3);
* `Algebra.Unramified.quotient`, `Algebra.GUnramified.quotient_of_fg`: item (4);
* `Algebra.GUnramified.of_etale`: item (5);
* `Algebra.exists_unramified_away_of_subsingleton_localizedModule` and its `gUnramified`
  variant: item (6);
* `Algebra.exists_unramified_away_of_subsingleton_fiber` and its `gUnramified` variant: item (7);
* `Algebra.exists_unramified_away_of_subsingleton_localizedModule_of_fiber` and its `gUnramified`
  variant: item (8);
* `Algebra.exists_unramified_away_of_subsingleton_fiber_of_fiber` and its `gUnramified` variant:
  item (9);
* `Algebra.Unramified.of_span_eq_top`, `Algebra.GUnramified.of_span_eq_top`: item (10);
* `Algebra.Unramified.of_forall_prime`, `Algebra.GUnramified.of_forall_prime`: item (11);
* `Algebra.GUnramified.exists_finiteType_int_baseChange`: item (12);
* `Algebra.Unramified.exists_finiteType_int_surjective`: item (13).

The `unramified` version of items (1), (2), (3) and (5) is Mathlib's — `Algebra.Unramified`
`.baseChange`, `.comp`, `.of_isLocalization_Away` and `Algebra.Etale.instUnramified` — so those
four items contribute only their `G-unramified` version to the list.

## Implementation notes

*One theorem, thirteen conjuncts, in the source's order.* The items share no data — each
quantifies over its own rings — so they are conjoined rather than gathered into a `TFAE` or a
structure. Inside a conjunct the two variants of the source's "resp." are a further conjunction, so
the `(resp. G-unramified)` reading of item `n` is the second component of item `n`.

*Every item is also exported under its own name, and the conjunction has three universe
parameters, not twenty-five.* A conjunction is not usable through its projections alone: a
declaration whose statement contains `n` occurrences of `Type*` carries `n` universe parameters,
and citing one conjunct leaves the levels of all the others as metavariables, which Lean refuses
outright — even for algebras in `Type`. Two things fix this together. The conjuncts share the
universe variables `u`, `v`, `w` instead of each introducing its own, which costs no generality
since the conjunction is universally quantified over them and no conjunct needs more than three
types at once; and each version of each item is exported as a named theorem that instantiates the
three levels, so a dependent proof cites `Algebra.GUnramified.of_etale` rather than a projection
path with a universe list. All of them carry the tag: a tag realized by several declarations is the
normal shape here.

*The exported items are theorems, not instances.* Items (1), (4) and (5) have the shape of an
instance, and their `unramified` counterparts are instances upstream. Declaring them as instances
here would give instance search a second route from `Algebra.Etale` or from a base change to
`Algebra.FiniteType` and `Algebra.FinitePresentation`, through `Algebra.GUnramified`'s fields and
so through this file, where Mathlib already has a direct one; the classes those goals belong to are
Mathlib's, and the shorter route should stay the only one. A user with `[Algebra.Etale R S]` in
context writes `Algebra.GUnramified.of_etale`.

*Being unramified is a hypothesis of the conjuncts, and an instance argument of the exported
items.* A conjunct with the same binders must serve both variants, so inside the conjunction the
finiteness and unramifiedness conditions are implications; the exported items take them as
instance arguments, as their Mathlib siblings do, so that instance search supplies them.

*Base change is stated on the tensor product, as Mathlib states it.* Item (1) concludes
`Algebra.Unramified R' (R' ⊗[R] S)`, the spelling of `Algebra.Unramified.baseChange`,
`Algebra.Smooth.baseChange` and `Algebra.Etale.baseChange`. The same statement for an arbitrary
model `S'` of the base change follows by transport along `Algebra.IsPushout.equiv`, since both
notions are invariant under `AlgEquiv` (`Algebra.Unramified.of_equiv`).

*A principal localization is read off an arbitrary model.* Item (3) is stated for any `Rf` with
`IsLocalization.Away f Rf`, not only for `Localization.Away f`, which is Mathlib's
`Algebra.Unramified.of_isLocalization_Away` and is the abstract form the source's `R_f` denotes.
In the items about a prime, however, `S_g` is `Localization.Away g`: there the localization is
existentially quantified, and pinning the model is what makes the existential a statement about
`S` and `g` alone. This is the spelling of Mathlib's
`Algebra.exists_unramified_of_isUnramifiedAt` and of Lemma 07BU.

*A quotient is taken of the base.* Item (4) is the source's `R → R ⧸ I`, not the more general
`R → A ⧸ I` for an unramified `R`-algebra `A` that `Algebra.FormallyUnramified.quotient` and
`Algebra.FinitePresentation.quotient` are stated for. Nothing is lost: the general form is item
(4) for `A ⧸ I` over `A` composed with `A` over `R` by item (2).

*Item (10) is stated for an arbitrary spanning set.* The source takes `g_1, …, g_m` generating the
unit ideal; `Ideal.span s = ⊤` for `s : Set S` is not weaker, since `1 ∈ Ideal.span s` already
gives a finite subset spanning the unit ideal, and it is the shape in which Mathlib phrases descent
along a principal cover of the target, as in `Algebra.IsLocalIso.of_span_eq_top` and
`RingHom.finiteType_ofLocalizationSpanTarget`, so no bridge is needed at the call sites.

*The differentials of the fibre are those of `κ(𝔭) ⊗_R S` over `κ(𝔭)`.* `Ideal.Fiber p S` is
Mathlib's `p.ResidueField ⊗[R] S`, which carries a global `κ(𝔭)`-algebra structure (the `S`-algebra
structure on a tensor product is only a local instance, so the fibre is written with `S` on the
right). Items (8) and (9) therefore quantify over a prime `q'` of the fibre rather than a prime
`q` of `S` lying over `𝔭`: the two are the same datum — `q` is the contraction of `q'`, and every
prime of the fibre lies over `𝔭`, which Mathlib supplies as an instance — and only this form makes
`κ(q')`, which is `κ(q)`, available as `q'.ResidueField` without constructing the prime of the
fibre by hand. Accordingly "`g ∉ q`" is written `Algebra.TensorProduct.includeRight g ∉ q'`. The
`_of_fiber` in the exported names of items (8) and (9) marks that the differentials whose stalk
resp. fibre vanishes are those of the fibre, the items being otherwise (6) and (7).

*Vanishing at a prime is `Subsingleton`, of a localization or of a fibre.* `(Ω_{S/R})_q = 0` is
`Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R])` and `Ω_{S/R} ⊗_S κ(q) = 0` is
`Subsingleton (q.Fiber Ω[S⁄R])`, i.e. `κ(q) ⊗_S Ω_{S/R}`; the source's tensor factors are in the
other order, which `TensorProduct.comm` undoes. `Subsingleton` rather than `= ⊥` because the
modules are types, and it is Mathlib's spelling in `Algebra.formallyUnramified_iff`.

*Descent is to a subring of `R`.* Items (12) and (13) produce `R₀` as a `Subring R` of finite type
over `ℤ`, which is the source's construction (a finitely generated `ℤ`-subalgebra of `R`
containing the coefficients of the equations) and pins the map `R₀ → R` to the inclusion; the
source only asks for some ring map `R₀ → R`, so this is the stronger form. `S₀` lives in the
universe of `R`, as the source's `R_0[x_1, …, x_n]/(…)` does. "`S = R ⊗_{R₀} S₀`" is
`Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀)`, an isomorphism of `R`-algebras rather than an equality of types,
and "`S` is a quotient of `R ⊗_{R₀} S₀`" is a surjective `R`-algebra map onto `S`.

Faithfulness to [Stacks 00UV]. (1) No hypothesis is idle: every conjunct's rings and primes occur
in its conclusion, each finiteness hypothesis is the one the source attaches to that variant, and
the theorem itself has no hypotheses — no Noetherian, flatness or finiteness assumption is placed
on any of the rings. (2) The scalars and the base are the source's: finite type, finite
presentation and `Ω` are taken over the source of the map in question — over `R'` after base
change in (1), over `R` in (6)–(13), over `κ(𝔭)` for the differentials of the fibre in (8)–(9) —
and `FiniteType ℤ R₀` in (12)–(13) is over `ℤ`, not over `R`. (3) The canonical maps are pinned:
`S_g` is `Localization.Away g` with its canonical map from `S`, the base change in (1) is the
tensor product with its two canonical maps, `R₀ → R` in (12)–(13) is the inclusion of a subring,
and the equivalence in (12) is one of `R`-algebras, so it commutes with the maps from `R`. (4) The
instantiation is not degenerate: `R → R` and `R → R_f` are G-unramified, so items (1)–(3) and
(10)–(13) all have witnesses with unramified inputs; and no conjunct is vacuous, since
`ℚ → ℚ[x]` is of finite presentation with `Ω` free of rank one, so it satisfies the finiteness
hypothesis of (6)–(9) and fails their vanishing hypothesis at every prime, and `{x}` spans a
proper ideal of `ℚ[x]`, so the spanning hypothesis of (10) is a real constraint.

## References

* [Stacks 00UV](https://stacks.math.columbia.edu/tag/00UV), Lemma 10.151.3, in Section 10.151
  "Unramified ring maps" (Section 00US). The definitions are Definition 00UT ([Stacks 00UT]) and
  the identification with formal unramifiedness is Lemma 00UU.
-/

@[expose] public section



open Algebra TensorProduct

/-- **Stacks 00UV.** Properties of unramified and G-unramified ring maps: (1) base change,
(2) composition, (3) a principal localization, (4) a quotient, (5) an étale map, (6)–(9) four
criteria at a prime in terms of the vanishing of the differentials, (10) descent along a principal
open cover, (11) unramifiedness at every prime, (12)–(13) descent to a finite type `ℤ`-algebra.
Each item has a version for `Algebra.Unramified` and one for `Algebra.GUnramified`, the source's
"resp.", differing only in whether the finiteness condition is finite type or finite
presentation. Cite the items by the names listed in the module docstring, not by projecting. -/
@[stacks 00UV "All thirteen items, both variants of each, as one conjunction in the source's
order; item `n` is the `n`-th conjunct and its `(resp. G-unramified)` reading is that conjunct's
second component. The conjuncts share the universe variables `u`, `v`, `w`, and each item is
exported under its own name; a proof should cite those names. Items (8) and (9) quantify over a
prime of the fibre `κ(𝔭) ⊗_R S` rather than over a prime of `S` lying over `𝔭`. See the module
docstring."]
public theorem Algebra.unramified_and_gUnramified_properties :
    -- (1) base change
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (R' : Type w)
        [CommRing R'] [Algebra R R'], (Unramified R S → Unramified R' (R' ⊗[R] S)) ∧
          (GUnramified R S → GUnramified R' (R' ⊗[R] S))) ∧
    -- (2) composition
    (∀ {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
        [Algebra S T] [Algebra R T] [IsScalarTower R S T],
        (Unramified R S → Unramified S T → Unramified R T) ∧
          (GUnramified R S → GUnramified S T → GUnramified R T)) ∧
    -- (3) a principal localization
    (∀ {R : Type u} [CommRing R] (f : R) (Rf : Type v) [CommRing Rf] [Algebra R Rf]
        [IsLocalization.Away f Rf], GUnramified R Rf ∧ Unramified R Rf) ∧
    -- (4) a quotient
    (∀ {R : Type u} [CommRing R] (I : Ideal R),
        Unramified R (R ⧸ I) ∧ (I.FG → GUnramified R (R ⧸ I))) ∧
    -- (5) an étale map
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Etale R S],
        GUnramified R S ∧ Unramified R S) ∧
    -- (6) the stalk of the differentials at the prime vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime],
        Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R]) →
          (FiniteType R S → ∃ g ∉ q, Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g ∉ q, GUnramified R (Localization.Away g))) ∧
    -- (7) the fibre of the differentials at the prime vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime],
        Subsingleton (q.Fiber Ω[S⁄R]) →
          (FiniteType R S → ∃ g ∉ q, Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g ∉ q, GUnramified R (Localization.Away g))) ∧
    -- (8) the stalk of the differentials of the fibre over `𝔭` vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (q : Ideal (p.Fiber S)) [q.IsPrime],
        Subsingleton (LocalizedModule q.primeCompl Ω[p.Fiber S⁄p.ResidueField]) →
          (FiniteType R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                GUnramified R (Localization.Away g))) ∧
    -- (9) the fibre at `q` of the differentials of the fibre over `𝔭` vanishes
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (q : Ideal (p.Fiber S)) [q.IsPrime],
        Subsingleton (q.Fiber Ω[p.Fiber S⁄p.ResidueField]) →
          (FiniteType R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                Unramified R (Localization.Away g)) ∧
            (FinitePresentation R S → ∃ g : S,
              Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
                GUnramified R (Localization.Away g))) ∧
    -- (10) descent along a cover of `Spec S` by principal opens
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (s : Set S),
        Ideal.span s = ⊤ →
        ((∀ g ∈ s, Unramified R (Localization.Away g)) → Unramified R S) ∧
          ((∀ g ∈ s, GUnramified R (Localization.Away g)) → GUnramified R S)) ∧
    -- (11) unramified at every prime
    (∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S],
        ((∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, Unramified R (Localization.Away g)) →
            Unramified R S) ∧
          ((∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, GUnramified R (Localization.Away g)) →
            GUnramified R S)) ∧
    -- (12) a G-unramified map is a base change of one over a finite type `ℤ`-algebra
    (∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S], GUnramified R S →
        ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
          FiniteType ℤ R₀ ∧ GUnramified R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀)) ∧
    -- (13) an unramified map is a quotient of a base change of one over a finite type `ℤ`-algebra
    (∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S], Unramified R S →
        ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
          (f : (R ⊗[R₀] S₀) →ₐ[R] S),
          FiniteType ℤ R₀ ∧ Unramified R₀ S₀ ∧ Function.Surjective f) :=
            by apply Stacks.Unramified.PermanenceProperties.solution

/-- **The base change of a G-unramified ring map is G-unramified** (Stacks 00UV (1)); item (1) of
`Algebra.unramified_and_gUnramified_properties`. This is `Algebra.Unramified.baseChange`, whose
statement is the other half of the item, with finite type replaced by finite presentation. -/
@[stacks 00UV "Item (1), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`; the `unramified` version is Mathlib's
`Algebra.Unramified.baseChange`.",
  ega "IV 17.3.3" "(iii) unramified, affine",
  ega "IV 17.1.3" "(iii) unram., affine", sga "1 I 3.5" "(iii), affine case"]
public theorem Algebra.GUnramified.baseChange (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] (B : Type w) [CommRing B] [Algebra R B] [GUnramified R A] :
    GUnramified B (B ⊗[R] A) :=
  (unramified_and_gUnramified_properties.{u, v, w}.1 (R := R) (S := A) B).2 ‹GUnramified R A›

/-- **The composition of G-unramified ring maps is G-unramified** (Stacks 00UV (2)); item (2) of
`Algebra.unramified_and_gUnramified_properties`. This is `Algebra.Unramified.comp`, whose statement
is the other half of the item, with finite type replaced by finite presentation. -/
@[stacks 00UV "Item (2), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`; the `unramified` version is Mathlib's
`Algebra.Unramified.comp`.",
  ega "IV 17.3.3" "(ii) unramified, affine",
  ega "IV 17.1.3" "(ii) unram., affine", sga "1 I 3.5" "(ii), affine case"]
public theorem Algebra.GUnramified.comp (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] (B : Type w) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [GUnramified R A] [GUnramified A B] : GUnramified R B :=
  (unramified_and_gUnramified_properties.{u, v, w}.2.1 (R := R) (S := A) (T := B)).2
    ‹GUnramified R A› ‹GUnramified A B›

/-- **A principal localization `R → R_r` is G-unramified** (Stacks 00UV (3)), stated for an
arbitrary model `A` of `R_r`; item (3) of `Algebra.unramified_and_gUnramified_properties`. This is
`Algebra.Unramified.of_isLocalization_Away`, whose statement is the other half of the item, with
finite type replaced by finite presentation. -/
@[stacks 00UV "Item (3), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`; the `unramified` version is Mathlib's
`Algebra.Unramified.of_isLocalization_Away`."]
public theorem Algebra.GUnramified.of_isLocalization_Away {R : Type u} [CommRing R] {A : Type v}
    [CommRing A] [Algebra R A] (r : R) [IsLocalization.Away r A] : GUnramified R A :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.1 r A).1

/-- **A quotient `R → R ⧸ I` is unramified** (Stacks 00UV (4), first sentence); item (4) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (4), first sentence, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.Unramified.quotient {R : Type u} [CommRing R] (I : Ideal R) :
    Unramified R (R ⧸ I) :=
  (unramified_and_gUnramified_properties.{u, 0, 0}.2.2.2.1 I).1

/-- **A quotient `R → R ⧸ I` by a finitely generated ideal is G-unramified** (Stacks 00UV (4),
second sentence); item (4) of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (4), second sentence, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.GUnramified.quotient_of_fg {R : Type u} [CommRing R] {I : Ideal R}
    (hI : I.FG) : GUnramified R (R ⧸ I) :=
  (unramified_and_gUnramified_properties.{u, 0, 0}.2.2.2.1 I).2 hI

/-- **An étale ring map is G-unramified** (Stacks 00UV (5)); item (5) of
`Algebra.unramified_and_gUnramified_properties`. This is `Algebra.Etale.instUnramified`, whose
statement is the other half of the item, with finite type replaced by finite presentation. -/
@[stacks 00UV "Item (5), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`; the `unramified` version is Mathlib's
`Algebra.Etale.instUnramified`."]
public theorem Algebra.GUnramified.of_etale {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    [Algebra R S] [Etale R S] : GUnramified R S :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.1 (R := R) (S := S)).1

/-- **A finite type ring map whose differentials have vanishing stalk at a prime `q` is unramified
at `q`** (Stacks 00UV (6)): there is a `g ∉ q` with `R → S_g` unramified. Item (6) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (6), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_unramified_away_of_subsingleton_localizedModule {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FiniteType R S] (q : Ideal S)
    [q.IsPrime] (hq : Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R])) :
    ∃ g ∉ q, Unramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.1 q hq).1 inferInstance

/-- **A finite presentation ring map whose differentials have vanishing stalk at a prime `q` is
G-unramified at `q`** (Stacks 00UV (6)): there is a `g ∉ q` with `R → S_g` G-unramified. Item (6)
of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (6), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_gUnramified_away_of_subsingleton_localizedModule {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FinitePresentation R S] (q : Ideal S)
    [q.IsPrime] (hq : Subsingleton (LocalizedModule q.primeCompl Ω[S⁄R])) :
    ∃ g ∉ q, GUnramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.1 q hq).2 inferInstance

/-- **A finite type ring map whose differentials have vanishing fibre at a prime `q` is unramified
at `q`** (Stacks 00UV (7)): there is a `g ∉ q` with `R → S_g` unramified. Item (7) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (7), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_unramified_away_of_subsingleton_fiber {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hq : Subsingleton (q.Fiber Ω[S⁄R])) : ∃ g ∉ q, Unramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.1 q hq).1 inferInstance

/-- **A finite presentation ring map whose differentials have vanishing fibre at a prime `q` is
G-unramified at `q`** (Stacks 00UV (7)): there is a `g ∉ q` with `R → S_g` G-unramified. Item (7)
of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (7), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_gUnramified_away_of_subsingleton_fiber {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    (hq : Subsingleton (q.Fiber Ω[S⁄R])) : ∃ g ∉ q, GUnramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.1 q hq).2 inferInstance

/-- **A finite type ring map whose fibre over `p` has differentials with vanishing stalk at a prime
`q` of that fibre is unramified at `q`** (Stacks 00UV (8)): there is a `g` in `S` whose image in
`κ(p) ⊗_R S` avoids `q` and with `R → S_g` unramified. Item (8) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (8), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_unramified_away_of_subsingleton_localizedModule_of_fiber
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : Subsingleton (LocalizedModule q.primeCompl Ω[p.Fiber S⁄p.ResidueField])) :
    ∃ g : S, Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
      Unramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.1 p q hq).1 inferInstance

/-- **A finite presentation ring map whose fibre over `p` has differentials with vanishing stalk at
a prime `q` of that fibre is G-unramified at `q`** (Stacks 00UV (8)): there is a `g` in `S` whose
image in `κ(p) ⊗_R S` avoids `q` and with `R → S_g` G-unramified. Item (8) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (8), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_gUnramified_away_of_subsingleton_localizedModule_of_fiber
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : Subsingleton (LocalizedModule q.primeCompl Ω[p.Fiber S⁄p.ResidueField])) :
    ∃ g : S, Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
      GUnramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.1 p q hq).2 inferInstance

/-- **A finite type ring map whose fibre over `p` has differentials with vanishing fibre at a prime
`q` of that fibre is unramified at `q`** (Stacks 00UV (9)): there is a `g` in `S` whose image in
`κ(p) ⊗_R S` avoids `q` and with `R → S_g` unramified. Item (9) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (9), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_unramified_away_of_subsingleton_fiber_of_fiber {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FiniteType R S] (p : Ideal R)
    [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : Subsingleton (q.Fiber Ω[p.Fiber S⁄p.ResidueField])) :
    ∃ g : S, Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
      Unramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.1 p q hq).1 inferInstance

/-- **A finite presentation ring map whose fibre over `p` has differentials with vanishing fibre at
a prime `q` of that fibre is G-unramified at `q`** (Stacks 00UV (9)): there is a `g` in `S` whose
image in `κ(p) ⊗_R S` avoids `q` and with `R → S_g` G-unramified. Item (9) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (9), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.exists_gUnramified_away_of_subsingleton_fiber_of_fiber {R : Type u}
    [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [FinitePresentation R S] (p : Ideal R)
    [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime]
    (hq : Subsingleton (q.Fiber Ω[p.Fiber S⁄p.ResidueField])) :
    ∃ g : S, Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField) g ∉ q ∧
      GUnramified R (Localization.Away g) :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.1 p q hq).2 inferInstance

/-- **Being unramified is local on the target**: if `s ⊆ S` generates the unit ideal and `R → S_g`
is unramified for every `g ∈ s`, then `R → S` is unramified (Stacks 00UV (10)); item (10) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (10), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.Unramified.of_span_eq_top {R : Type u} [CommRing R] {S : Type v}
    [CommRing S] [Algebra R S] {s : Set S} (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, Unramified R (Localization.Away g)) : Unramified R S :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.1 s hs).1 H

/-- **Being G-unramified is local on the target**: if `s ⊆ S` generates the unit ideal and
`R → S_g` is G-unramified for every `g ∈ s`, then `R → S` is G-unramified (Stacks 00UV (10));
item (10) of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (10), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.GUnramified.of_span_eq_top {R : Type u} [CommRing R] {S : Type v}
    [CommRing S] [Algebra R S] {s : Set S} (hs : Ideal.span s = ⊤)
    (H : ∀ g ∈ s, GUnramified R (Localization.Away g)) : GUnramified R S :=
  (unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.1 s hs).2 H

/-- **A ring map unramified at every prime of the target is unramified** (Stacks 00UV (11));
item (11) of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (11), the `unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.Unramified.of_forall_prime {R : Type u} [CommRing R] {S : Type v}
    [CommRing S] [Algebra R S]
    (H : ∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, Unramified R (Localization.Away g)) :
    Unramified R S :=
  unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.2.1.1 H

/-- **A ring map G-unramified at every prime of the target is G-unramified** (Stacks 00UV (11));
item (11) of `Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (11), the `G-unramified` version, exported from
`Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.GUnramified.of_forall_prime {R : Type u} [CommRing R] {S : Type v}
    [CommRing S] [Algebra R S]
    (H : ∀ (q : Ideal S) [q.IsPrime], ∃ g ∉ q, GUnramified R (Localization.Away g)) :
    GUnramified R S :=
  unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.2.1.2 H

/-- **A G-unramified ring map is a base change of a G-unramified map over a finite type
`ℤ`-algebra** (Stacks 00UV (12)): there are a subring `R₀ ⊆ R` of finite type over `ℤ` and a
G-unramified `R₀`-algebra `S₀` with `S ≃ R ⊗_{R₀} S₀` as `R`-algebras. Item (12) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (12), exported from `Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.GUnramified.exists_finiteType_int_baseChange {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [GUnramified R S] :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      FiniteType ℤ R₀ ∧ GUnramified R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) :=
  unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.2.2.1 inferInstance

/-- **An unramified ring map is a quotient of a base change of an unramified map over a finite type
`ℤ`-algebra** (Stacks 00UV (13)): there are a subring `R₀ ⊆ R` of finite type over `ℤ` and an
unramified `R₀`-algebra `S₀` with a surjection `R ⊗_{R₀} S₀ → S` of `R`-algebras. Item (13) of
`Algebra.unramified_and_gUnramified_properties`. -/
@[stacks 00UV "Item (13), exported from `Algebra.unramified_and_gUnramified_properties`."]
public theorem Algebra.Unramified.exists_finiteType_int_surjective {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Unramified R S] :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
      (f : (R ⊗[R₀] S₀) →ₐ[R] S),
      FiniteType ℤ R₀ ∧ Unramified R₀ S₀ ∧ Function.Surjective f :=
  unramified_and_gUnramified_properties.{u, v, 0}.2.2.2.2.2.2.2.2.2.2.2.2 inferInstance

end
