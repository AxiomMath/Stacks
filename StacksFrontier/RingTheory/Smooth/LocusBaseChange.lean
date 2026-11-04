module

import StacksFrontier.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.RingTheory.Smooth.Locus
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.RingTheory.Cotangent.H1BaseChange

@[expose] public section

/-!
# The smooth locus is stable under flat base change

Let `R → S` be a ring map of finite presentation, let `R → R'` be flat and let `S'` be the base
change `R' ⊗_R S`.  This file proves Stacks 00TG: the set of primes of `S'` at which `R' → S'` is
smooth is the inverse image, under `f : Spec(S') → Spec(S)`, of the set of primes of `S` at which
`R → S` is smooth.

The proof is the source's.  Formation of the naive cotangent complex commutes with flat base
change (Lemma 00S4), so `Ω_{S'/R'} = S' ⊗_S Ω_{S/R}` and `H_1(L_{S'/R'}) = S' ⊗_S H_1(L_{S/R})`.
Since the smooth locus of a finitely presented algebra is the locus where `H_1` vanishes and `Ω`
is locally free, everything is reduced to two facts about the flat base change `S → S'`: the
support of a module and the free locus of a finitely presented module both pull back to those of
the base change.  Each is read at a prime `q'` of `S'` lying over `q ⊆ S`, where the local map
`S_q → S'_{q'}` is flat, hence faithfully flat (Lemma 00HR); the support then pulls back because a
faithfully flat base change reflects vanishing, and freeness descends because flatness does
(Lemma 00O1: a finitely presented flat module over a local ring is free).

## Main results

* `Stacks.Smooth.LocusFlatBaseChange.solution`: Lemma 00TG.

## Implementation notes

`Algebra.smoothLocus_eq_compl_support_inter` is Mathlib's form of the criterion of Lemma 07BU that
the two proofs share, so the argument is run on `Module.support` and `Module.freeLocus` rather than
one prime at a time.  Of the two base change statements this needs, Mathlib has the inclusion `⊆`
of the second one, `Module.comap_freeLocus_le`, which holds without flatness; the converse
inclusion is flat descent of freeness, `free_of_free_baseChange`, and that is where Lemma 00O1
enters.

Mathlib has Lemma 00S4 for `H_1` only in the shape `Algebra.tensorH1CotangentOfFlat`, over the
model `R' ⊗[R] S`, whereas the statement here is over an abstract base change
`Algebra.IsPushout R S R' S'` and needs the comparison along `S → S'`, not along `R → R'`.  Two
steps bridge the gap. `isBaseChange_restrictScalars_h1Cotangent_map` transports the model statement
along `Algebra.IsPushout.equiv`, the point being the functoriality `h1Cotangent_map_map` of
`Algebra.H1Cotangent.map` in the algebra, which Mathlib states only for extensions
(`Algebra.Extension.H1Cotangent.map_comp`, together with `map_eq`: the induced map does not depend
on the chosen hom of extensions).  `isBaseChange_of_isBaseChange_of_isPushout` then turns a base
change along `R → R'` into one along `S → S'`, by the cancellation `S' ⊗[S] M ≃ R' ⊗[R] M` of
`Algebra.IsPushout.cancelBaseChange`; that second step is a general fact about modules over a
pushout square, the module-level counterpart of `Algebra.IsPushout.comp_iff`, whose Kähler analogue
Mathlib already builds by hand as `KaehlerDifferential.tensorKaehlerEquiv` out of
`KaehlerDifferential.isBaseChange`.

## References

* [StacksProject 00TG](https://stacks.math.columbia.edu/tag/00TG)
  (`algebra-lemma-smooth-base-change`), in the section "Smooth ring maps".
-/

namespace Stacks.Smooth.LocusFlatBaseChange

open TensorProduct

/-- Vanishing of the localization of `M` at `p`, read on an arbitrary model of it.  The sibling of
`Module.mem_freeLocus_of_isLocalization` for the support; `Module.notMem_support_iff` is the case
`f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M`. -/
private lemma notMem_support_iff_subsingleton {A M Mp : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup Mp] [Module A Mp] (p : PrimeSpectrum A) (f : M →ₗ[A] Mp)
    [IsLocalizedModule p.asIdeal.primeCompl f] :
    p ∉ Module.support A M ↔ Subsingleton Mp := by
  rw [Module.notMem_support_iff]
  exact (IsLocalizedModule.iso p.asIdeal.primeCompl f).subsingleton_congr

/-- The base change of `X` to `D` computed through two intermediate algebras `B` and `C` of
`A → D`: both sides are `D ⊗[A] X`, by `TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
private noncomputable def baseChangeComparison (A B C D : Type*) [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D]
    [Algebra C D] [IsScalarTower A B D] [IsScalarTower A C D] (X : Type*) [AddCommGroup X]
    [Module A X] : D ⊗[B] (B ⊗[A] X) ≃ₗ[D] D ⊗[C] (C ⊗[A] X) :=
  AlgebraTensorModule.cancelBaseChange A B D D X ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A C D D X).symm

/-- **Flat descent of freeness over a local ring** (Stacks 00O1).  If `A → B` is faithfully flat,
`A` is local and `M` is a finitely presented `A`-module whose base change `B ⊗[A] M` is free, then
`M` itself is free: flatness descends along a faithfully flat base change, and a finitely presented
flat module over a local ring is free. -/
@[sga "1 VIII 1.11" "special case"]
private lemma free_of_free_baseChange (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] [Module.Free B (B ⊗[A] M)] : Module.Free A M :=
  have : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M B
  Module.free_of_flat_of_isLocalRing

section Flat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

/-- At a prime `P` of `B` over `p`, the localization map `A_p → B_P` of a flat `A → B` is
faithfully flat (Lemma 00HR), and `B_P` is an `A_p`-algebra compatible with `A`. -/
private lemma exists_faithfullyFlat_localization (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] (p : Ideal A) (P : Ideal B) [p.IsPrime]
    [P.IsPrime] [P.LiesOver p] :
    ∃ _ : Algebra (Localization.AtPrime p) (Localization.AtPrime P),
      IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime P) ∧
      Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime P) := by
  let alg := Localization.AtPrime.algebraOfLiesOver p P
  exact ⟨alg, inferInstance, .of_flat_of_isLocalHom⟩

/-- Along a flat ring map `A → B` the support of a module pulls back to the support of its base
change.  At a prime `P` of `B` lying over `p` the local map `A_p → B_P` is flat, hence faithfully
flat (Lemma 00HR), and a faithfully flat base change reflects vanishing. -/
private lemma comap_support_eq_of_flat (N : Type*) [AddCommGroup N] [Module A N] :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.support A N
      = Module.support B (B ⊗[A] N) := by
  ext P
  set p := PrimeSpectrum.comap (algebraMap A B) P with hp
  have : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  obtain ⟨_, _, _⟩ := exists_faithfullyFlat_localization A p.asIdeal P.asIdeal
  set Ap := Localization.AtPrime p.asIdeal
  set Bp := Localization.AtPrime P.asIdeal
  rw [Set.mem_preimage, ← not_iff_not, ← hp,
    notMem_support_iff_subsingleton p (TensorProduct.mk A Ap N 1),
    notMem_support_iff_subsingleton P (TensorProduct.mk B Bp (B ⊗[A] N) 1),
    (baseChangeComparison A B Ap Bp N).subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right Ap Bp]

/-- Along a flat ring map `A → B` the free locus of a finitely presented module pulls back to the
free locus of its base change.  One inclusion is `Module.comap_freeLocus_le`, which needs no
flatness; the other is `free_of_free_baseChange` over the local ring `A_p`. -/
private lemma comap_freeLocus_eq_of_flat (M : Type*) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' Module.freeLocus A M
      = Module.freeLocus B (B ⊗[A] M) := by
  refine Module.comap_freeLocus_le.antisymm fun P hP ↦ ?_
  set p := PrimeSpectrum.comap (algebraMap A B) P with hp
  have : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  obtain ⟨_, _, _⟩ := exists_faithfullyFlat_localization A p.asIdeal P.asIdeal
  set Ap := Localization.AtPrime p.asIdeal
  set Bp := Localization.AtPrime P.asIdeal
  rw [Module.mem_freeLocus_iff_tensor P Bp,
    Module.Free.iff_of_equiv (baseChangeComparison A B Ap Bp M)] at hP
  rw [Set.mem_preimage, ← hp, Module.mem_freeLocus_iff_tensor p Ap]
  exact free_of_free_baseChange Ap Bp _

end Flat

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The smooth locus is stable under flat base change** (Stacks 00TG). -/
@[ega "IV 17.7.2" "(ii), affine case"]
public theorem solution (R S R' S' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.FinitePresentation R S] [Module.Flat R R'] :
    PrimeSpectrum.comap (algebraMap S S') ⁻¹' Algebra.smoothLocus R S
      = Algebra.smoothLocus R' S' := by
  have hpo : Algebra.IsPushout R R' S S' := .symm inferInstance
  have : Module.Flat S S' :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R S R' S').toLinearEquiv.symm
  have : Algebra.FinitePresentation R' S' :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R R' S S')
  rw [Algebra.smoothLocus_eq_compl_support_inter, Algebra.smoothLocus_eq_compl_support_inter,
    Set.preimage_inter, Set.preimage_compl, comap_support_eq_of_flat, comap_freeLocus_eq_of_flat,
    (Stacks.Cotangent.H1BaseChange.isBaseChange_h1Cotangent_map R S R' S').equiv.support_eq,
    Module.freeLocus_congr (KaehlerDifferential.tensorKaehlerEquiv R R' S S')]

end Stacks.Smooth.LocusFlatBaseChange

/-!
# The smooth locus is stable under flat base change

Let `R → S` be a ring map of finite presentation, let `R → R'` be a flat ring map and let
`S' = R' ⊗_R S` be the base change. Write `U ⊆ Spec(S)` for the set of primes at which `R → S` is
smooth and `V ⊆ Spec(S')` for the set of primes at which `R' → S'` is smooth (both open, by
Lemma 00TF). Then `V` is exactly the inverse image of `U` under `f : Spec(S') → Spec(S)`, the map
induced by `S → S'`.

The source's proof. Formation of the naive cotangent complex commutes with base change: `NL_{S/R}
⊗_S S'` is homotopy equivalent to `NL_{S'/R'}` (Lemma 00S4). Since smoothness is stable under base
change this already gives `f^{-1}(U) ⊆ V`, and no flatness is needed for that inclusion. For the
converse let `q' ⊆ S'` be a prime lying over `q ⊆ S` with `q' ∈ V`. Flatness of `R → R'` makes
`S → S'` flat, so the local ring map `S_q → S'_{q'}` is a flat local map, hence faithfully flat
(Lemma 00HR). The vanishing of `H_1(L_{S'/R'})_{q'} = H_1(L_{S/R})_q ⊗_{S_q} S'_{q'}` therefore
forces `H_1(L_{S/R})_q = 0`, and flat descent of projectivity along a faithfully flat map
(Lemma 00O1) applied to the finitely presented `S_q`-module `(Ω_{S/R})_q` makes it projective.
By Lemma 07BU these two conditions say `R → S` is smooth at `q`, that is `q ∈ U`.

Flatness of `R → R'` is load-bearing, not decoration: for `R = k[t]`, `S = k[t, x]/(tx)` and the
non-flat base change `R' = k[t]/(t) = k` one gets `S' = k[x]`, which is smooth over `k` everywhere,
while `R → S` is not smooth at the crossing point `q = (t, x)` — there `H_1(L_{S/R})_q` is the
non-zero annihilator ideal of `t`. So `V = Spec(S')` while `f^{-1}(U)` misses the prime `(x)`.

## Main results

* `Algebra.smoothLocus_comap_of_isPushout`: Lemma 00TG, the smooth locus of a flat base change of
  a finitely presented algebra is the preimage of the smooth locus.

## Implementation notes

The base change is the abstract one: `S'` is any commutative ring making the square of scalar
towers `R → S`, `R → R'`, `R' → S'`, `S → S'` a pushout, `Algebra.IsPushout R S R' S'`, rather
than the model `R' ⊗[R] S`. The model `S ⊗[R] R'` is a witness, by the instance
`TensorProduct.isPushout`, and stating the instance rather than the construction is what lets a
consumer apply the lemma to the base change already in hand.

`U` and `V` are `Algebra.smoothLocus R S` and `Algebra.smoothLocus R' S'`, Mathlib's smooth loci,
whose members are the primes `p` with `S_p` formally smooth over the base. For a finitely presented
algebra this is the source's Definition 00TB, the existence of `g ∉ p` with `S_g` smooth
(`Algebra.basicOpen_subset_smoothLocus_iff_smooth` together with `Algebra.isOpen_smoothLocus`, and
Lemma 07BU); so the reading of `V` is the source's as well, since
`Algebra.FinitePresentation R' S'` is automatic here — it is
`Algebra.FinitePresentation.baseChange` transported along `Algebra.IsPushout.equiv R R' S S'`.

The equality is oriented as `f^{-1}(U) = V`, matching the sibling
`Algebra.smoothLocus_comap_of_isLocalization`, from whose name this one is mutated; the source
writes `V = f^{-1}(U)`.

The hypothesis is the source's `Module.Flat R R'`, although the proof only ever uses flatness of
`S → S'`, which follows from it by `Module.Flat.isBaseChange` applied to `Algebra.IsPushout.out`.
Weakening the hypothesis to `Module.Flat S S'` would be a genuine generalization, but one whose
extra content is the exotic case of a non-flat `R → R'` whose base change along `S` happens to be
flat, and it would cost every call site that one-line bridge; the flat-base-change hypothesis is
also the one Mathlib carries in siblings such as `Algebra.rankAtStalk_eq_of_isPushout`.

Faithfulness to the source, point by point. (1) No hypothesis is idle: `Module.Flat R R'` is what
gives the inclusion `V ⊆ f^{-1}(U)` and fails without it, as the `k[t, x]/(tx)` example above
shows; `Algebra.FinitePresentation R S` is what makes `Algebra.smoothLocus R S` the source's `U`
and what makes `(Ω_{S/R})_q` finitely presented, so that flat descent gives projectivity; and
`Algebra.IsPushout R S R' S'` is what makes the naive cotangent complex of `S'/R'` the base change
of that of `S/R`, hence gives `f^{-1}(U) ⊆ V`. (2) The scalars and the bases are the source's:
`U` is the smooth locus of `S` over `R` and `V` that of `S'` over `R'`, not over `R`, and the
preimage is along the structure map `S → S'` of the base change. (3) The canonical map is pinned:
`f` is `PrimeSpectrum.comap (algebraMap S S')`, the map on spectra induced by `S → S'`, and `S'` is
pinned as the base change by the pushout instance rather than asserted to exist. (4) The
instantiation is not degenerate: for `R = ℚ[t]`, `S = ℚ[t][x]/(x² - t)`, the flat base change
`R' = ℚ[t, s]` and `S' = ℚ[t, s][x]/(x² - t)`, both `U` and `V` are the non-empty proper open
complements of the closed subset `x = 0`, so neither side is empty and neither is everything.

## References

* [StacksProject 00TG](https://stacks.math.columbia.edu/tag/00TG)
  (`algebra-lemma-smooth-base-change`), in the section "Smooth ring maps". Smoothness at a prime is
  Definition 00TB, and the openness of `U` and `V` is Lemma 00TF.

## Tags

smooth ring map, smooth locus, flat base change, naive cotangent complex
-/

@[expose] public section

/-- **The smooth locus is stable under flat base change** (Stacks 00TG). Let `R → S` be of finite
presentation, let `R → R'` be flat and let `S'` be the base change `R' ⊗_R S`. Then the set of
primes of `S'` at which `R' → S'` is smooth is the inverse image, under
`f : Spec(S') → Spec(S)`, of the set of primes of `S` at which `R → S` is smooth. -/
@[stacks 00TG "The base change is the abstract one, `Algebra.IsPushout R S R' S'`, and the two
smooth loci are Mathlib's `Algebra.smoothLocus`, which for a finitely presented algebra is the
source's set of primes at which the map is smooth (Definition 00TB, via Lemma 07BU). The equality
is oriented as `f⁻¹(U) = V`, as in `Algebra.smoothLocus_comap_of_isLocalization`. See the module
docstring.", sga "1 II 4.13" "affine case", ega "IV 17.7.2" "(ii), affine case"]
public theorem Algebra.smoothLocus_comap_of_isPushout (R S R' S' : Type*) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.FinitePresentation R S] [Module.Flat R R'] :
    PrimeSpectrum.comap (algebraMap S S') ⁻¹' Algebra.smoothLocus R S
      = Algebra.smoothLocus R' S' := by apply Stacks.Smooth.LocusFlatBaseChange.solution

end

/-!
# Smoothness at a prime is insensitive to base field extension

Let `k` be a field, let `S` be a finite type `k`-algebra, let `K` be a `k`-algebra and let `S'` be
the base change `K ⊗_k S`. Let `q'` be a prime of `S'` and let `q` be the prime of `S` it lies
over. This file proves Stacks 02UQ: `S` is smooth over `k` at `q` if and only if `S'` is smooth
over `K` at `q'`.

The proof is the source's: this is the special case of Lemma 00TG — the smooth locus of a flat base
change of a finitely presented algebra is the preimage of the smooth locus — in which the base is a
field. Read at a single prime, Lemma 00TG says exactly that `S` is smooth over `R` at `q` if and
only if the base change is smooth at a prime over `q`, and that is the auxiliary
`isSmoothAt_iff_isSmoothAt_of_isPushout` below. Over a field both of its hypotheses are free: every
module over a field is free, hence flat, so `k → K` is flat by instance search, and a field is
Noetherian, so a finite type `k`-algebra is of finite presentation.

## Main results

* `Stacks.Smooth.FieldExtensionInvariance.solution`: Lemma 02UQ, smoothness at a prime is unchanged
  by extending the base field.

## Implementation notes

The auxiliary lemma is stated over an arbitrary base ring, since nothing in the passage from a
locus to a point uses the base: it is the pointwise form of Lemma 00TG, and it is the sibling of
`Algebra.smoothLocus_comap_of_isPushout` that Mathlib does not carry. The prime of `S` cut out by
`q'` is `q'.under S = Ideal.comap (algebraMap S S') q'`, which is `q` by `Ideal.over_def`, and it
is the ideal underlying the point `PrimeSpectrum.comap (algebraMap S S') q'` at which the locus
equality is evaluated.

## References

* [StacksProject 02UQ](https://stacks.math.columbia.edu/tag/02UQ)
  (`algebra-lemma-smooth-field-extension`), in the section "Smooth ring maps".
-/

namespace Stacks.Smooth.FieldExtensionInvariance

/-- **The smooth locus of a flat base change, read at one prime.** Let `R → S` be of finite
presentation, let `R → R'` be flat and let `S'` be the base change `R' ⊗_R S`. Then `S` is smooth
over `R` at a prime `q` if and only if `S'` is smooth over `R'` at a prime `q'` lying over `q`.

This is Lemma 00TG (`Algebra.smoothLocus_comap_of_isPushout`), an equality of subsets of
`Spec(S')`, evaluated at the point `q'`. Lemma 02UQ is the case of a field base, where both
hypotheses are automatic. -/
@[ega "IV 17.7.2" "(ii), affine case"]
public theorem isSmoothAt_iff_isSmoothAt_of_isPushout (R S R' S' : Type*) [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S']
    [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.FinitePresentation R S] [Module.Flat R R']
    (q : Ideal S) (q' : Ideal S') [q.IsPrime] [q'.IsPrime] [q'.LiesOver q] :
    Algebra.IsSmoothAt R q ↔ Algebra.IsSmoothAt R' q' := by
  obtain rfl : q = q'.under S := q'.over_def q
  exact Set.ext_iff.mp (Algebra.smoothLocus_comap_of_isPushout R S R' S') ⟨q', ‹_›⟩

/-- **Smoothness at a prime is insensitive to base field extension** (Stacks 02UQ). Let `k` be a
field, `S` a finite type `k`-algebra, `K` a `k`-algebra and `S'` the base change `K ⊗_k S`. Let
`q'` be a prime of `S'` lying over the prime `q` of `S`. Then `S` is smooth over `k` at `q` if and
only if `S'` is smooth over `K` at `q'`. -/
public theorem solution {k S K S' : Type*} [Field k]
    [CommRing S] [CommRing K] [CommRing S'] [Algebra k S] [Algebra k K] [Algebra S S']
    [Algebra K S'] [Algebra k S'] [IsScalarTower k K S'] [IsScalarTower k S S']
    [Algebra.IsPushout k S K S'] [Algebra.FiniteType k S] (q : Ideal S) (q' : Ideal S')
    [q.IsPrime] [q'.IsPrime] [q'.LiesOver q] :
    Algebra.IsSmoothAt k q ↔ Algebra.IsSmoothAt K q' :=
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  isSmoothAt_iff_isSmoothAt_of_isPushout k S K S' q q'

end Stacks.Smooth.FieldExtensionInvariance

/-!
# Smoothness at a prime is insensitive to base field extension

Let `k` be a field, let `S` be a finite type `k`-algebra and let `S'` be the base change of `S`
along a `k`-algebra `K`, so `S' = K ⊗_k S`. Let `q'` be a prime of `S'` and let `q` be the prime
of `S` it lies over. Then `S` is smooth over `k` at `q` if and only if `S'` is smooth over `K`
at `q'`.

The source's proof is one sentence: this is the special case of Lemma 00TG (the smooth locus of a
flat base change of a finitely presented algebra is the preimage of the smooth locus) in which the
base is a field. Over a field the two hypotheses of that lemma are free: every `k`-module is flat,
so `k → K` is flat with nothing to check, and a field is Noetherian, so a finite type `k`-algebra
is of finite presentation (`Algebra.FinitePresentation.of_finiteType`). That is the whole content
of the specialization, and it is why the statement below asks only for `Algebra.FiniteType k S`.

## Main results

* `Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout`: Lemma 02UQ, smoothness at a prime is unchanged
  by extending the base field.

## Implementation notes

`K` is an arbitrary commutative `k`-algebra, not a field extension of `k` as in the source. The
field-ness of `K` is used nowhere: what the proof needs of `k → K` is flatness, which over a field
`k` holds for every `k`-algebra. Keeping `Field K` would be a hypothesis the conclusion does not
use, and the source's case `K/k` is recovered by `Field K` plus `Algebra k K`. The hypothesis
`Field k` is genuinely used, twice, as described above.

The base change is the abstract one, `Algebra.IsPushout k S K S'`: `S'` is any commutative ring
making the square of scalar towers `k → S`, `k → K`, `K → S'`, `S → S'` a pushout, rather than the
model `S ⊗[k] K`. That model is a witness, by `TensorProduct.isPushout`, so nothing is lost, and
stating the instance lets a consumer apply the lemma to the base change already in hand. This
matches the sibling `Algebra.smoothLocus_comap_of_isPushout` (Lemma 00TG), from whose name this
one is mutated by passing to a single prime.

The correspondence of primes is `Ideal.LiesOver`: `[q'.LiesOver q]` says `q = q'.under S`, that
is `q = Ideal.comap (algebraMap S S') q'`, which is the source's "corresponding prime". The same
idiom carries the prime correspondence in Mathlib's `Algebra.IsSmoothAt.of_formallySmooth_fiber`.
Smoothness at a prime is Mathlib's `Algebra.IsSmoothAt`, formal smoothness of the localization;
for an algebra of finite presentation this is the source's Definition 00TB, the existence of
`g ∉ q` with `S_g` smooth (`Algebra.basicOpen_subset_smoothLocus_iff_smooth` with
`Algebra.isOpen_smoothLocus`, and Lemma 07BU), and `Algebra.FinitePresentation K S'` holds on the
right as well, being `Algebra.FinitePresentation.baseChange` transported along
`Algebra.IsPushout.equiv k K S S'`.

Faithfulness to the source, point by point. (1) No hypothesis is idle: `Field k` gives flatness of
`k → K` and Noetherianity, both of which fail for a general base (for `k = ℤ`, `K = 𝔽_p`,
`S = ℤ[x, y]/(py)` the right side is smooth at the image of `q = (p, y)` while the left side is
not); `Algebra.FiniteType k S` is what makes `Algebra.IsSmoothAt` the source's notion and what
makes `(Ω_{S/k})_q` finitely presented; `Algebra.IsPushout k S K S'` is what makes `S'` the base
change `S_K` rather than an unrelated ring; and `q'.LiesOver q` is what makes `q` the prime
corresponding to `q'`. (2) The scalars and the bases are the source's: the left side is smoothness
of `S` over `k`, the right side smoothness of `S'` over `K`, not over `k`. (3) The canonical map is
pinned: the prime correspondence is comap along the structure map `algebraMap S S'`, spelled by
`LiesOver`, and `S'` is pinned as the base change by the pushout instance rather than merely
asserted to exist. (4) The instantiation is not degenerate, in both directions: take `k = ℚ`,
`K = ℚ(√2)`, `S = ℚ[x, y]/(y² - x³)` and `S' = K ⊗_ℚ S`; at `q = (x, y)` neither side is smooth,
while at `q = (x - 1, y - 1)` both are, so neither implication is vacuous and neither side is
constant.

## References

* [StacksProject 02UQ](https://stacks.math.columbia.edu/tag/02UQ)
  (`algebra-lemma-smooth-field-extension`), in the section "Smooth ring maps". Smoothness at a
  prime is Definition 00TB, and the lemma is a special case of Lemma 00TG.

## Tags

smooth ring map, smooth locus, base field extension, base change
-/

@[expose] public section

/-- **Smoothness at a prime is insensitive to base field extension** (Stacks 02UQ). Let `k` be a
field, `S` a finite type `k`-algebra, `K` a `k`-algebra and `S'` the base change `K ⊗_k S`. Let
`q'` be a prime of `S'` lying over the prime `q` of `S`. Then `S` is smooth over `k` at `q` if and
only if `S'` is smooth over `K` at `q'`. -/
@[stacks 02UQ "The source takes `K/k` a field extension; `K` is here an arbitrary commutative
`k`-algebra, since only flatness of `k → K` is used and that is automatic over a field. The base
change is the abstract one, `Algebra.IsPushout k S K S'`, the prime correspondence is
`Ideal.LiesOver`, and smoothness at a prime is Mathlib's `Algebra.IsSmoothAt`, which for a finite
type algebra over a field is the source's Definition 00TB. See the module docstring."]
public theorem Algebra.isSmoothAt_iff_isSmoothAt_of_isPushout {k S K S' : Type*} [Field k]
    [CommRing S] [CommRing K] [CommRing S'] [Algebra k S] [Algebra k K] [Algebra S S']
    [Algebra K S'] [Algebra k S'] [IsScalarTower k K S'] [IsScalarTower k S S']
    [Algebra.IsPushout k S K S'] [Algebra.FiniteType k S] (q : Ideal S) (q' : Ideal S')
    [q.IsPrime] [q'.IsPrime] [q'.LiesOver q] :
    Algebra.IsSmoothAt k q ↔ Algebra.IsSmoothAt K q' :=
    by apply Stacks.Smooth.FieldExtensionInvariance.solution

end
