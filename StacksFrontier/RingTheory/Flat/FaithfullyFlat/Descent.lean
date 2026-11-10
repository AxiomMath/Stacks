module

import StacksFrontier.RingTheory.Nilpotent.Descent
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute


@[expose] public section

universe uR uS uM uT

/-!
# Descent of finiteness properties

A finiteness property of a module or an algebra can often be checked after a base change and
deduced over the base ring. This file collects such descent statements for two kinds of base
change: along a faithfully flat ring map, and along a localization of the base ring or a
quotient of one.

Let `S` be faithfully flat over `R`. A module whose base change to `S` is of finite presentation,
finite projective or countably generated is again so over `R`, an `R`-algebra whose base change
is of finite type is again so over `R`, and being Noetherian and being reduced descend from `S`
to `R`. What drives the module statements is that a faithfully flat base change reflects
surjectivity, so a generating family or a family of relations found over `S` may be replaced by
one found over `R`.

Let `S ⊆ R` be a multiplicative subset. A finite `S⁻¹R`-module of the form `S⁻¹M` already comes
from `R`: finiteness of `S⁻¹M` is witnessed by the images of finitely many `x₁, …, xₙ ∈ M`, and
for the resulting `ψ : Rⁿ → M` the quotient `M' = Rⁿ ⧸ K` maps to `M` with `S⁻¹M' ≅ S⁻¹M` as soon
as `K ≤ Ker ψ` is `S`-saturated in `Ker ψ`. Taking `K = Ker ψ` makes `M'` finite; taking for `K`
the relations obtained by clearing denominators in a finite generating family of the relations
over `S⁻¹R` — available when `S⁻¹M` is finitely presented — makes `M'` of finite presentation.
The same argument run over a quotient `R'` of `S⁻¹R` writes a finite `R'`-module as a base change
`R' ⊗[R] M`.

Finally, a map `f : S →ₐ[R] S'` of `R`-algebras with `S` of finite type and `S'` of finite
presentation and flat is an isomorphism as soon as it is one modulo an ideal `I ⊆ R` all of whose
elements are nilpotent. Surjectivity of the reduction makes `f` surjective, and Nakayama applied
to `J = Ker f` makes it injective: `J` is finitely generated, injectivity of the reduction gives
`J ≤ IS`, flatness of `S'` upgrades this to `J ≤ IS · J`, and `IS` consists of nilpotents, hence
lies in the Jacobson radical of `S`.

## Main definitions

* `Module.CountablyGenerated`: a module is spanned by an at most countable set of its elements.

## Main results

* `Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat`: finite presentation of a module
  descends along a faithfully flat base change.
* `Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat`: projectivity of a finite
  module descends along a faithfully flat base change.
* `countablyGenerated_of_faithfullyFlat_baseChange`: countable generation descends along a
  faithfully flat base change.
* `descent_noetherian`, `RingHom.FaithfullyFlat.isReduced`: a ring faithfully flat over which
  there is a Noetherian, resp. reduced, ring is itself Noetherian, resp. reduced.
* `Algebra.FiniteType.iff_finiteType_tensorProduct`: an algebra is of finite type if and only if
  its faithfully flat base change is.
* `Module.exists_finite_isLocalizedModule_comp`: a module whose localization at `S` is a finite
  `S⁻¹R`-module receives a map from a finite `R`-module inducing an isomorphism of localizations,
  from a finitely presented one when `S⁻¹M` is finitely presented.
* `Module.exists_finite_isLocalizedModule_comp_atPrime`: the same at `S = p.primeCompl`.
* `Module.exists_finite_isBaseChange_of_surjective_algebraMap`: a finite module over a quotient
  `R'` of `S⁻¹R` is the base change of a finite `R`-module, of a finitely presented one when it
  is finitely presented.
* `AlgHom.bijective_of_bijective_quotientMapₐ_of_le_nilradical`: an algebra map that is an
  isomorphism modulo an ideal of nilpotents is an isomorphism.

## Implementation notes

Base changes and localizations are taken abstractly rather than through a model: a base change of
`M` to `S` is an `S`-module `N` with an `R`-linear `f : M →ₗ[R] N` such that `IsBaseChange S f`,
and a localization of `M` at `S` is an `R`-algebra `Rₛ` with `IsLocalization S Rₛ` together with
`f : M →ₗ[R] Mₛ` satisfying `IsLocalizedModule S f`. The concrete `M ⊗_R S`, `S⁻¹R` and `S⁻¹M`
instantiate this with `S ⊗[R] M` and `f = TensorProduct.mk R S M 1`, resp. `Localization S` and
`LocalizedModule S M` with `f = LocalizedModule.mkLinearMap S M`. Following Mathlib, the base
ring is written on the left of the tensor product where the sources write `M ⊗_R S`; the two
agree by `TensorProduct.comm`.

For the same reason the isomorphism a source asserts is pinned to the map inducing it, rather
than quantified over a choice of model: `IsBaseChange R' g` names the map `R' ⊗_R M → M'`,
`r' ⊗ x ↦ r' • g x`, and `IsLocalizedModule S (f ∘ₗ φ)` says that `Mₛ`, viewed through
`M' → M → Mₛ`, is a localization of `M'` at `S`. For a chosen localization `f' : M' →ₗ[R] M'ₛ`
the latter is equivalent, by `IsLocalizedModule.map_comp` and
`IsLocalizedModule.comp_iff_of_bijective_left`, to bijectivity of the induced
`IsLocalizedModule.map S f' f φ : S⁻¹M' → S⁻¹M`, from which `IsLocalizedModule.linearEquiv`
produces the isomorphism `S⁻¹M' ≅ S⁻¹M` the source asserts.

In 05GJ, 05N5 and 05N6 the two items are one statement about one module, the finitely presented
case appearing as an implication conjunct; this is equivalent to their conjunction, since a
finitely presented module is finite. The module produced lives in the universe of `R`, both
constructions being quotients of `Rⁿ`, and no injectivity is claimed: in the finitely presented
case `K` is in general strictly smaller than the module of relations. Rings are `CommRing`s and
modules `AddCommGroup`s because a quotient by a submodule is what the constructions produce.

Only two features of the ring map `R → S⁻¹(R/I)` of 05N5 are used: every element of `S` becomes
invertible, and the ring is generated by the image of `R` together with those inverses. That says
exactly that it is a quotient of `S⁻¹R`, so that is the hypothesis made, with the ideal `I`
playing no further role; the source's own case is `R' = Rₛ ⧸ I.map (algebraMap R Rₛ)` with
`hsurj := Ideal.Quotient.mk_surjective`. Lemma 05GJ is the case `S = p.primeCompl` of 05N6 and
nothing more, `IsLocalization.AtPrime Rₚ p` being an abbreviation for
`IsLocalization p.primeCompl Rₚ`.

That an ideal consists of nilpotents is spelled `I ≤ nilradical R`, the spelling that composes
with the radical and Jacobson API. The reduction `S/IS → S'/IS'` is `Ideal.quotientMapₐ` applied
to `f`, with its side condition `IS ≤ (IS').comap f` discharged inline so that the statement
carries no hypothesis a user must supply, and the conclusion is `Function.Bijective f` rather than
an `S ≃ₐ[R] S'`, the equivalence being `AlgEquiv.ofBijective f`. The source localises at each
prime of `S` in order to put the ideal that Nakayama consumes inside a Jacobson radical; here
`I ≤ nilradical R` puts `IS` inside the nilradical of `S` already, so no prime and no
localisation occur below.

The hypotheses are sharp. Flatness in 07RE cannot be dropped: over `R = k[ε]/(ε²)` with `I = (ε)`
the quotient map `R[x] → R[x]/(εx)` is bijective modulo `ε` and of finite presentation, and is
not injective, its target `R ⊕ ⨁_{n ≥ 1} R/(ε)` not being flat. Nor can finiteness of `S⁻¹M` in
05N6: for `S = 1` the conclusion says that `M` itself is finite. The finiteness hypothesis of
`Module.Projective.of_finite_of_isBaseChange_of_faithfullyFlat` is used by the argument but is not
needed for the truth of the conclusion — Theorem 05A9 removes it by a Kaplansky dévissage — so
the name records it, leaving the unqualified name for 05A9.

## References

* [StacksProject 00QP](https://stacks.math.columbia.edu/tag/00QP)
* [StacksProject 00QQ](https://stacks.math.columbia.edu/tag/00QQ)
* [StacksProject 033E](https://stacks.math.columbia.edu/tag/033E)
* [StacksProject 033F](https://stacks.math.columbia.edu/tag/033F)
* [StacksProject 03C4](https://stacks.math.columbia.edu/tag/03C4)
* [StacksProject 058S](https://stacks.math.columbia.edu/tag/058S)
* [StacksProject 05GJ](https://stacks.math.columbia.edu/tag/05GJ)
* [StacksProject 05N5](https://stacks.math.columbia.edu/tag/05N5)
* [StacksProject 05N6](https://stacks.math.columbia.edu/tag/05N6)
* [StacksProject 07RE](https://stacks.math.columbia.edu/tag/07RE)
* [StacksProject 0GVD](https://stacks.math.columbia.edu/tag/0GVD)
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module

/-- Let `R → S` be faithfully flat, let `l : P → M` be a surjection of `R`-modules with `P` finite
over `R`, and assume the base change `S ⊗[R] M` is a finitely presented `S`-module. Then
`ker l` is a finitely generated `R`-module. -/
@[ega "IV 2.5.3" "special case"]
private theorem fg_ker_of_faithfullyFlat {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R P] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation S (S ⊗[R] M)] (l : P →ₗ[R] M) (hl : Function.Surjective l) :
    (LinearMap.ker l).FG := by
  rw [← Module.Finite.iff_fg]
  have : Module.Finite S (S ⊗[R] (LinearMap.ker l)) := by
    rw [Module.Finite.equiv_iff (LinearMap.tensorKerEquiv S S l), Module.Finite.iff_fg]
    exact Module.FinitePresentation.fg_ker _
      ((Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S l).mpr hl)
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- **Stacks 03C4** (part 2). Let `R → S` be a faithfully flat ring map, let `M` be an `R`-module
and let `f : M →ₗ[R] N` exhibit the `S`-module `N` as the base change of `M` along `R → S`. If `N`
is a finitely presented `S`-module, then `M` is a finitely presented `R`-module. -/
@[stacks 03C4 "Part (2). Part (1) is `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`
and part (3) is `Module.Flat.of_flat_tensorProduct`, both in Mathlib.",
  ega "IV 2.5.2"
  "(ii), descent, affine",
  ega "IV 2.5.3" "fin. pres., descent",
  sga "1 VIII 1.11"
    "fin. pres., descent",
  sga "1 VIII 1.10" "fin. pres., affine",
  sga "4½ Arcata 1.4.2"
      "(ii), fin. presentation"]
theorem FinitePresentation.of_isBaseChange_of_faithfullyFlat {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (h : IsBaseChange S f) [Module.FinitePresentation S N] :
    Module.FinitePresentation R M := by
  have : Module.FinitePresentation S (S ⊗[R] M) :=
    (LinearEquiv.finitePresentation_iff h.equiv).mpr ‹_›
  have : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hsurj := (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp hs
  exact Module.finitePresentation_of_free_of_surjective _ hsurj
    (fg_ker_of_faithfullyFlat S _ hsurj)

/-- **Stacks 058S** (the projectivity half). Let `R → S` be a faithfully flat ring map, let `M` be
an `R`-module and let `f : M →ₗ[R] N` exhibit the `S`-module `N` as the base change of `M` along
`R → S`. If `N` is a finite projective `S`-module, then `M` is a projective `R`-module. Together
with `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` this says that being a finite
projective module descends along a faithfully flat ring map. -/
@[stacks 058S "The projectivity half of the conclusion; the finiteness half is Mathlib's
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.",
  sga "1 VIII 1.10" "loc. free, affine",
  sga "3 VIB 11.8.2" "finite projective case",
  sga "3 VIB 11.8.1" "(ii), special case",
  sga "3 VIB 11.9.1" "special case"]
theorem Projective.of_finite_of_isBaseChange_of_faithfullyFlat {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) (h : IsBaseChange S f)
    [Module.Finite S N] [Module.Projective S N] :
    Module.Projective R M := by
  have : Module.FinitePresentation S N := Module.finitePresentation_of_projective S N
  have : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat f h
  have : Module.Flat S (S ⊗[R] M) := Module.Flat.of_linearEquiv h.equiv
  have : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
  exact Module.Flat.projective_of_finitePresentation

/-- An `R`-module `M` is *countably generated* if there is an at most countable set of elements of
`M` whose `R`-span is all of `M`. Here `Set.Countable` means "finite or countably infinite",
matching the informal "at most countable" condition. -/
def CountablyGenerated (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : Prop :=
  ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤

/-- A finitely generated module is countably generated. -/
theorem CountablyGenerated.of_finite
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.CountablyGenerated R M := by
  obtain ⟨s, hs⟩ := (Module.finite_def (R := R) (M := M)).mp ‹_›
  exact ⟨(s : Set M), s.finite_toSet.countable, hs⟩

/-- The image of a countably generated module under a surjective linear map is countably
generated. -/
theorem CountablyGenerated.of_surjective {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (h : Module.CountablyGenerated R M) : Module.CountablyGenerated R N := by
  obtain ⟨s, hsc, hspan⟩ := h
  refine ⟨f '' s, hsc.image f, ?_⟩
  rw [← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-- Countable generation is invariant under linear equivalences. -/
theorem CountablyGenerated.of_linearEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.CountablyGenerated R M) : Module.CountablyGenerated R N :=
  of_surjective (e : M →ₗ[R] N) e.surjective h

/-- A module is countably generated iff there is a surjective `R`-linear map onto it
from a free module `R^(I)` on an at most countable index set `I`. -/
theorem CountablyGenerated.iff_exists_surjective
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    Module.CountablyGenerated R M ↔
      ∃ (I : Type) (_ : Countable I) (f : (I →₀ R) →ₗ[R] M), Function.Surjective f := by
  constructor
  · rintro ⟨s, hsc, hspan⟩
    obtain ⟨g, hg⟩ := (hsc.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
    exact ⟨ℕ, inferInstance, Finsupp.linearCombination R g,
      (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mp
        (by rwa [← hg, Submodule.span_insert_zero])⟩
  · rintro ⟨I, hI, f, hf⟩
    have hfeq : f = Finsupp.linearCombination R fun i => f (Finsupp.single i 1) :=
      Finsupp.lhom_ext' fun i => LinearMap.ext_ring (by simp)
    exact ⟨Set.range fun i : I => f (Finsupp.single i 1), Set.countable_range _,
      (span_range_eq_top_iff_surjective_finsuppLinearCombination R).mpr (hfeq ▸ hf)⟩

end Module

/-- **Stacks 0GVD**. Let `R → S` be a faithfully flat ring map and let `M` be an `R`-module.
If the base change `S ⊗[R] M` is countably generated as an `S`-module, then `M` is countably
generated as an `R`-module. -/
@[stacks 0GVD]
theorem countablyGenerated_of_faithfullyFlat_baseChange
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    (h : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M := by
  classical
  obtain ⟨Y, hYc, hYspan⟩ := h
  choose fs hfs using fun y : Y => TensorProduct.exists_finset (y : S ⊗[R] M)
  have : Countable ↑Y := hYc.to_subtype
  set s : Set M := ⋃ y : Y, Prod.snd '' (fs y : Set (S × M))
  refine ⟨s, Set.countable_iUnion fun y => ((fs y).finite_toSet.image _).countable, ?_⟩
  set M' : Submodule R M := Submodule.span R s
  rw [← Submodule.range_subtype M', LinearMap.range_eq_top,
    ← Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S M'.subtype]
  change Function.Surjective (LinearMap.baseChange S M'.subtype)
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hYspan, Submodule.span_le]
  intro y hy
  have hy' : y = ∑ p ∈ fs ⟨y, hy⟩, p.1 ⊗ₜ[R] p.2 := hfs ⟨y, hy⟩
  rw [SetLike.mem_coe, hy']
  refine Submodule.sum_mem _ fun p hp => ⟨p.1 ⊗ₜ[R] ⟨p.2, ?_⟩, by simp⟩
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨y, hy⟩, p, hp, rfl⟩)

/-- **Stacks 033E**. If `φ : R → S` is faithfully flat and `S` is Noetherian, then `R` is
Noetherian. -/
@[stacks 033E, ega "0 6.5.2" "special case", ega "IV 2.2.14" "affine source and target"]
theorem descent_noetherian {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.FaithfullyFlat) (hS : IsNoetherianRing S) : IsNoetherianRing R := by
  algebraize [φ]
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
    (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)

/-- **Stacks 033F**. If `φ : R → S` is a faithfully flat ring map and `S` is reduced,
then `R` is reduced. -/
@[stacks 033F, ega "IV 11.3.13" "(i), reduced case"]
theorem RingHom.FaithfullyFlat.isReduced {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : φ.FaithfullyFlat) [IsReduced S] : IsReduced R :=
  ⟨fun _ hx => RingHom.FaithfullyFlat.injective hφ ((hx.map φ).eq_zero.trans (map_zero φ).symm)⟩

/-- **Stacks 00QP**. Being of finite type descends along a faithfully flat base change:
for a faithfully flat `R`-algebra `R'`, an `R`-algebra `S` is of finite type if and only
if `R' ⊗[R] S` is of finite type over `R'`. -/
@[stacks 00QP, sga "1 VIII 3.4", sga "1 VIII 3.3" "finite type, affine"]
theorem Algebra.FiniteType.iff_finiteType_tensorProduct
    (R S R' : Type*) [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] [Module.FaithfullyFlat R R'] :
    Algebra.FiniteType R S ↔ Algebra.FiniteType R' (R' ⊗[R] S) :=
  ⟨fun _ ↦ Algebra.FiniteType.baseChange R',
    fun _ ↦ Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat R'⟩

/- Stacks 00QQ, both directions, are Mathlib's: `Algebra.FinitePresentation.baseChange` is the
ascending direction (which needs no flatness) and
`Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` is the
descending one. Both are stated at the algebra level; the source's ring map `R → S` is
`algebraMap R S`, and `RingHom.finitePresentation_algebraMap` passes between the two spellings.
At the ring-map level the same pair is `RingHom.finitePresentation_isStableUnderBaseChange` and
`RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`. -/
add_to_stacks 00QQ "a base change of an algebra of finite presentation is of finite presentation"
  Algebra.FinitePresentation.baseChange
add_to_stacks 00QQ "finite presentation descends along a faithfully flat base change"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_sga "1 VIII 3.6" "affine case"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_sga "3 VIB 10.8" "special case"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_sga "3 XIX 2.1" "special case"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_sga "6 VIII 1.6" "special case"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.7.1" "special case"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
add_to_ega "IV 2.7.1.1" "partial"
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat

namespace Module

/-- To find a submodule `K ≤ L` with a property `P` that is finitely generated under a hypothesis
`Q`, it suffices that `L` has `P` and that `Q` yields a finitely generated `K ≤ L` with `P`. -/
private theorem exists_le_and_fg_of_imp {R F : Type*} [CommRing R] [AddCommGroup F]
    [Module R F] (L : Submodule R F) (P : Submodule R F → Prop) (Q : Prop) (hL : P L)
    (h : Q → ∃ K : Submodule R F, K.FG ∧ K ≤ L ∧ P K) :
    ∃ K : Submodule R F, K ≤ L ∧ P K ∧ (Q → K.FG) := by
  by_cases hQ : Q
  · obtain ⟨K, hfg, hle, hP⟩ := h hQ
    exact ⟨K, hle, hP, fun _ => hfg⟩
  · exact ⟨L, le_rfl, hL, fun h => absurd h hQ⟩

section Localization

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (Rₛ : Type v) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M : Type w} [AddCommGroup M] [Module R M]
  {Mₛ : Type t} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
  (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

include S in
/-- A finite `Rₛ`-module which is a localization of `M` at `S` is generated over `Rₛ` by the
images of finitely many elements of `M`. -/
private theorem exists_fin_span_range_comp [Module.Finite Rₛ Mₛ] :
    ∃ (n : ℕ) (t : Fin n → M), Submodule.span Rₛ (Set.range fun i => f (t i)) = ⊤ := by
  obtain ⟨n, y, hy⟩ := Module.Finite.exists_fin (R := Rₛ) (M := Mₛ)
  choose p hp using fun i => IsLocalizedModule.surj S f (y i)
  refine ⟨n, fun i => (p i).1, top_unique (hy ▸ Submodule.span_le.2 ?_)⟩
  rintro _ ⟨i, rfl⟩
  refine (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units Rₛ (p i).2)).1 ?_
  rw [algebraMap_smul, ← Submonoid.smul_def, hp i]
  exact Submodule.subset_span ⟨i, rfl⟩

variable {F : Type*} [AddCommGroup F] [Module R F]
  {Fₛ : Type*} [AddCommGroup Fₛ] [Module R Fₛ] [Module Rₛ Fₛ] [IsScalarTower R Rₛ Fₛ]

include S in
/-- If `ι : F → Fₛ` is a localization of `F` at `S` and the image of `x : F` lies in the
`Rₛ`-span of the image of `w ⊆ F`, then `(s : R) • x` lies in the `R`-span of `w` for some
`s ∈ S`. -/
private theorem exists_smul_mem_span (ι : F →ₗ[R] Fₛ) [IsLocalizedModule S ι] (w : Set F)
    {x : F} (hx : ι x ∈ Submodule.span Rₛ (ι '' w)) :
    ∃ s : S, (s : R) • x ∈ Submodule.span R w := by
  rw [← Submodule.localized'_span Rₛ S ι] at hx
  obtain ⟨y, hy, s, hs⟩ := hx
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def] at hs
  obtain ⟨e, he⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := ι)
    (x₁ := y) (x₂ := (s : R) • x) (by rw [hs, map_smul])
  exact ⟨e * s, by
    rw [Submonoid.coe_mul, mul_smul, ← show (e : R) • y = (e : R) • (s : R) • x by
      simpa [Submonoid.smul_def] using he]
    exact Submodule.smul_mem _ _ hy⟩

/-- If `ι : F → Fₛ` and `f : M → Mₛ` are localizations at `S`, if `Ψ : Fₛ → Mₛ` is `Rₛ`-linear
with `Ψ ∘ ι = f ∘ ψ`, and if `Ker Ψ` is a finitely generated `Rₛ`-module, then `Ker ψ` contains a
finitely generated submodule in which it is `S`-saturated. -/
private theorem exists_fg_saturated_le_ker (ι : F →ₗ[R] Fₛ) [IsLocalizedModule S ι]
    (ψ : F →ₗ[R] M) (Ψ : Fₛ →ₗ[Rₛ] Mₛ) (hcomp : ∀ x : F, Ψ (ι x) = f (ψ x))
    (hfg : (LinearMap.ker Ψ).FG) :
    ∃ K : Submodule R F, K.FG ∧ K ≤ LinearMap.ker ψ ∧
      ∀ z ∈ LinearMap.ker ψ, ∃ c : S, (c : R) • z ∈ K := by
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hkmem : ∀ j, Ψ (k j) = 0 := fun j =>
    LinearMap.mem_ker.1 (hk.le (Submodule.subset_span ⟨j, rfl⟩))
  have hlift : ∀ j, ∃ (z : F) (c : S), (c : R) • k j = ι z := fun j =>
    let ⟨⟨z, c⟩, hc⟩ := IsLocalizedModule.surj S ι (k j); ⟨z, c, hc⟩
  choose z c hc using hlift
  have hz : ∀ j, ∃ d : S, (d : R) • ψ (z j) = 0 := fun j => by
    obtain ⟨d, hd⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f)
      (show f (ψ (z j)) = f 0 by
        rw [map_zero, ← hcomp, ← hc j, Ψ.map_smul_of_tower, hkmem j, smul_zero])
    exact ⟨d, by simpa [Submonoid.smul_def] using hd⟩
  choose d hd using hz
  obtain ⟨w, hw⟩ : ∃ w : Fin m → F, ∀ j, w j = (d j : R) • z j := ⟨_, fun _ => rfl⟩
  have hwker : ∀ j, w j ∈ LinearMap.ker ψ := fun j => by
    rw [LinearMap.mem_ker, hw j, map_smul, hd j]
  have hspan : Submodule.span Rₛ (ι '' Set.range w) = LinearMap.ker Ψ := by
    rw [← Set.range_comp]
    refine le_antisymm (Submodule.span_le.2 ?_) (hk ▸ Submodule.span_le.2 ?_)
    · rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, Function.comp_apply, LinearMap.mem_ker, hcomp,
        LinearMap.mem_ker.1 (hwker j), map_zero]
    · rintro _ ⟨j, rfl⟩
      refine (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units Rₛ (d j * c j))).1 ?_
      rw [algebraMap_smul, Submonoid.coe_mul, mul_smul, hc j, ← map_smul, ← hw j]
      exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨Submodule.span R (Set.range w), Submodule.fg_span (Set.finite_range w),
    Submodule.span_le.2 (Set.range_subset_iff.2 hwker), fun x hx =>
      exists_smul_mem_span S Rₛ ι _ ?_⟩
  rw [hspan, LinearMap.mem_ker, hcomp, LinearMap.mem_ker.1 hx, map_zero]

/-- Let `f : M → Mₛ` be a localization of `M` at `S`, let `ψ : F → M` be
`R`-linear with `S⁻¹F → Mₛ` surjective (spelled: every `y : Mₛ` has `s • y = f (ψ x)`) and let
`K ≤ Ker ψ` be a submodule in which `Ker ψ` is `S`-saturated. Then `Mₛ`, viewed through
`F ⧸ K → M → Mₛ`, is a localization of `F ⧸ K` at `S`. -/
private theorem isLocalizedModule_comp_liftQ (ψ : F →ₗ[R] M)
    (K : Submodule R F) (hK : K ≤ LinearMap.ker ψ)
    (hsurj : ∀ y : Mₛ, ∃ (x : F) (s : S), s • y = f (ψ x))
    (hsat : ∀ z ∈ LinearMap.ker ψ, ∃ c : S, (c : R) • z ∈ K) :
    IsLocalizedModule S (f ∘ₗ K.liftQ ψ hK) where
  map_units s := IsLocalizedModule.map_units f s
  surj y := by
    obtain ⟨x, s, hs⟩ := hsurj y
    exact ⟨⟨K.mkQ x, s⟩, by simpa using hs⟩
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨a₁, rfl⟩ := K.mkQ_surjective x₁
    obtain ⟨a₂, rfl⟩ := K.mkQ_surjective x₂
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.liftQ_apply] at h
    obtain ⟨c₁, hc₁⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) h
    obtain ⟨c₂, hc₂⟩ := hsat ((c₁ : R) • (a₁ - a₂)) <| by
      simp only [LinearMap.mem_ker, map_smul, map_sub, smul_sub, sub_eq_zero]
      exact hc₁
    refine ⟨c₂ * c₁, ?_⟩
    rwa [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, ← sub_eq_zero, ← smul_sub,
      ← map_sub, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mul_smul]

/-- **Stacks 05N6.** Let `R` be a ring, `S ⊆ R` a multiplicative subset, `M` an `R`-module and
`f : M → Mₛ` a localization of `M` at `S`, over a localization `Rₛ` of `R` at `S`.

1. If `Mₛ = S⁻¹M` is a finite `Rₛ`-module, then there is a finite `R`-module `M'` and an
   `R`-linear map `φ : M' → M` inducing an isomorphism `S⁻¹M' ≅ S⁻¹M`, spelled
   `IsLocalizedModule S (f ∘ₗ φ)`.
2. If `Mₛ` is moreover a finitely presented `Rₛ`-module, then `M'` is of finite presentation
   over `R`. -/
@[stacks 05N6 "Localizations are abstract (`IsLocalization S Rₛ`, `IsLocalizedModule S f`); the
induced isomorphism `S⁻¹M' → S⁻¹M` is pinned as `IsLocalizedModule S (f ∘ₗ φ)`; `M'` is produced
in the universe of `R`. Items (1) and (2) are the two conjuncts, (2) as an implication about the
same `M'`."]
theorem exists_finite_isLocalizedModule_comp {R : Type u} [CommRing R] (S : Submonoid R)
    (Rₛ : Type v) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {M : Type w} [AddCommGroup M] [Module R M]
    {Mₛ : Type t} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] [Module.Finite Rₛ Mₛ] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (φ : M' →ₗ[R] M),
      Module.Finite R M' ∧ IsLocalizedModule S (f ∘ₗ φ) ∧
        (Module.FinitePresentation Rₛ Mₛ → Module.FinitePresentation R M') := by
  obtain ⟨n, t, ht⟩ := exists_fin_span_range_comp S Rₛ f
  let ψ := Fintype.linearCombination R t
  have hψ : ∀ x, ψ x = ∑ i, x i • t i := Fintype.linearCombination_apply R t
  let Ψ := Fintype.linearCombination Rₛ fun i => f (t i)
  have hΨ : ∀ a, Ψ a = ∑ i, a i • f (t i) := Fintype.linearCombination_apply Rₛ _
  have hΨsurj : Function.Surjective Ψ :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination Rₛ _).mp ht
  let ι : (Fin n → R) →ₗ[R] (Fin n → Rₛ) :=
    LinearMap.pi fun i => (Algebra.linearMap R Rₛ) ∘ₗ LinearMap.proj i
  have hcomp : ∀ x : Fin n → R, Ψ (ι x) = f (ψ x) := fun x => by
    rw [hΨ, hψ, map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show ι x i = algebraMap R Rₛ (x i) from rfl, algebraMap_smul, map_smul]
  have hsurj : ∀ y : Mₛ, ∃ (x : Fin n → R) (s : S), s • y = f (ψ x) := fun y => by
    obtain ⟨a, rfl⟩ := hΨsurj y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S ι a
    exact ⟨x, s, by
      rw [← hcomp x, ← hs]
      exact (Ψ.map_smul_of_tower (s : R) a).symm⟩
  obtain ⟨K, hKle, hKsat, hKfg⟩ := exists_le_and_fg_of_imp (LinearMap.ker ψ)
    (fun K => ∀ z ∈ LinearMap.ker ψ, ∃ c : S, (c : R) • z ∈ K) (Module.FinitePresentation Rₛ Mₛ)
    (fun z hz => ⟨1, by simpa using hz⟩) fun _ =>
      exists_fg_saturated_le_ker S Rₛ f ι ψ Ψ hcomp (Module.FinitePresentation.fg_ker Ψ hΨsurj)
  exact ⟨(Fin n → R) ⧸ K, inferInstance, inferInstance, K.liftQ ψ hKle, inferInstance,
    isLocalizedModule_comp_liftQ S f ψ K hKle hsurj hKsat, fun hfp =>
      Module.finitePresentation_of_free_of_surjective K.mkQ K.mkQ_surjective
        (by simpa using hKfg hfp)⟩

/-- **Stacks 05GJ.** Let `R` be a ring, `p ⊆ R` a prime ideal, `M` an `R`-module and
`f : M → Mₚ` a localization of `M` at `p.primeCompl`, over a localization `Rₚ` of `R` at `p`.

1. If `Mₚ` is a finite `Rₚ`-module, then there is a finite `R`-module `M'` and an `R`-linear map
   `φ : M' → M` inducing an isomorphism `M'ₚ ≅ Mₚ`, spelled
   `IsLocalizedModule p.primeCompl (f ∘ₗ φ)`.
2. If `Mₚ` is moreover a finitely presented `Rₚ`-module, then `M'` is of finite presentation
   over `R`. -/
@[stacks 05GJ "The case `S = p.primeCompl` of 05N6
(`Module.exists_finite_isLocalizedModule_comp`), stated in the same shape: localizations are
abstract, the induced isomorphism `M'ₚ → Mₚ` is pinned as
`IsLocalizedModule p.primeCompl (f ∘ₗ φ)`, `M'` is produced in the universe of `R`, and items (1)
and (2) are the two conjuncts, (2) as an implication about the same `M'`."]
theorem exists_finite_isLocalizedModule_comp_atPrime {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (Rₚ : Type v) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    {M : Type w} [AddCommGroup M] [Module R M]
    {Mₚ : Type t} [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl f] [Module.Finite Rₚ Mₚ] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (φ : M' →ₗ[R] M),
      Module.Finite R M' ∧ IsLocalizedModule p.primeCompl (f ∘ₗ φ) ∧
        (Module.FinitePresentation Rₚ Mₚ → Module.FinitePresentation R M') :=
  exists_finite_isLocalizedModule_comp p.primeCompl Rₚ f

end Localization

section BaseChange

variable {R : Type u} [CommRing R] (S : Submonoid R) (Rₛ : Type v) [CommRing Rₛ]
  [Algebra R Rₛ] [IsLocalization S Rₛ] {R' : Type w} [CommRing R'] [Algebra R R']
  [Algebra Rₛ R'] [IsScalarTower R Rₛ R'] {M : Type*} [AddCommGroup M] [Module R M]

include S Rₛ

/-- The image in `R'` of an element of `S` is a unit. -/
private theorem isUnit_algebraMap (s : S) : IsUnit (algebraMap R R' (s : R)) := by
  rw [IsScalarTower.algebraMap_apply R Rₛ R']
  exact (IsLocalization.map_units Rₛ s).map (algebraMap Rₛ R')

/-- Every element of `R' ⊗[R] M` becomes of the form `1 ⊗ₜ m` after multiplication by the image
of an element of `S`. -/
private theorem exists_smul_eq_one_tmul (hsurj : Function.Surjective (algebraMap Rₛ R'))
    (t : R' ⊗[R] M) :
    ∃ (s : S) (m : M), (algebraMap R R' (s : R)) • t = (1 : R') ⊗ₜ[R] m := by
  obtain ⟨u, rfl⟩ := LinearMap.rTensor_surjective M
    (g := (Algebra.linearMap Rₛ R').restrictScalars R) hsurj t
  obtain ⟨⟨m, s⟩, hms⟩ : ∃ x : M × S, (x.2 : R) • u = (1 : Rₛ) ⊗ₜ[R] x.1 :=
    IsLocalizedModule.surj S (TensorProduct.mk R Rₛ M 1) u
  exact ⟨s, m, by
    rw [algebraMap_smul, ← map_smul, hms]
    simp⟩

/-- For a surjection `Rₛ → R'` from a localization `Rₛ = S⁻¹R`, an `R`-linear map `g : M → M'`
into an `R'`-module exhibits `M'` as the base change of `M` to `R'` as soon as its range spans
`M'` over `R'` and its kernel dies in `R' ⊗[R] M`. -/
private theorem isBaseChange_of_ker_le (hsurj : Function.Surjective (algebraMap Rₛ R'))
    {M' : Type t} [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (g : M →ₗ[R] M') (hspan : Submodule.span R' (LinearMap.range g : Set M') = ⊤)
    (hker : LinearMap.ker g ≤ LinearMap.ker (TensorProduct.mk R R' M 1)) :
    IsBaseChange R' g := by
  have hbij : Function.Bijective (g.liftBaseChange R') := by
    refine ⟨?_, by rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, hspan]⟩
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨s, m, hsm⟩ := exists_smul_eq_one_tmul S Rₛ hsurj z
    have h := congrArg (g.liftBaseChange R') hsm
    rw [map_smul, LinearMap.mem_ker.mp hz, smul_zero, LinearMap.liftBaseChange_tmul,
      one_smul] at h
    refine ((isUnit_algebraMap S Rₛ (R' := R') s).smul_eq_zero).mp ?_
    rw [hsm]
    exact LinearMap.mem_ker.mp (hker (LinearMap.mem_ker.mpr h.symm))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun x => by simp

variable {F : Type*} [AddCommGroup F] [Module R F]
  {F' : Type*} [AddCommGroup F'] [Module R F'] [Module R' F'] [IsScalarTower R R' F']
  {ι : F →ₗ[R] F'} {M' : Type t} [AddCommGroup M'] [Module R M'] [Module R' M']
  [IsScalarTower R R' M']

/-- Denominators can be cleared: along a base change `ι : F → F'` to `R'`, some element of `S`
takes a given element of `F'` into the range of `ι`. -/
private theorem exists_smul_mem_range (hsurj : Function.Surjective (algebraMap Rₛ R'))
    (hι : IsBaseChange R' ι) (y : F') :
    ∃ (s : S) (z : F), (algebraMap R R' (s : R)) • y = ι z := by
  obtain ⟨p, hp⟩ := hι.equiv.surjective y
  obtain ⟨s, z, hsz⟩ := exists_smul_eq_one_tmul S Rₛ hsurj p
  exact ⟨s, z, by rw [← hp, ← map_smul, hsz, hι.equiv_tmul, one_smul]⟩

/-- Let `ι : F → F'` be a base change to `R'`, let `φ : F → M'` have `R'`-spanning range and let
`K ≤ Ker φ` be a submodule whose image in `F'` spans the image of `Ker φ` over `R'`. Then `M'` is
the base change of `F ⧸ K` to `R'` along the map induced by `φ`. -/
private theorem isBaseChange_liftQ (hsurj : Function.Surjective (algebraMap Rₛ R'))
    (hι : IsBaseChange R' ι) (φ : F →ₗ[R] M')
    (hspan : Submodule.span R' (LinearMap.range φ : Set M') = ⊤)
    (K : Submodule R F) (hK : K ≤ LinearMap.ker φ)
    (hKK : ∀ c : F, φ c = 0 → ι c ∈ Submodule.span R' (ι '' K)) :
    IsBaseChange R' (K.liftQ φ hK) := by
  refine isBaseChange_of_ker_le S Rₛ hsurj _ (by rwa [Submodule.range_liftQ]) ?_
  obtain ⟨ν, hν⟩ : ∃ ν : F' →ₗ[R'] R' ⊗[R] (F ⧸ K),
      ∀ c : F, ν (ι c) = (1 : R') ⊗ₜ[R] (K.mkQ c) :=
    ⟨hι.lift ((TensorProduct.mk R R' (F ⧸ K) 1) ∘ₗ K.mkQ), fun c => hι.lift_eq _ c⟩
  have hker : Submodule.span R' (ι '' K) ≤ LinearMap.ker ν := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    simp [hν, (Submodule.Quotient.mk_eq_zero K).mpr hk]
  intro y hy
  obtain ⟨c, rfl⟩ := K.mkQ_surjective y
  have h := hker (hKK c (by simpa using hy))
  rw [LinearMap.mem_ker, hν c] at h
  simpa using h

/-- If `M'` is finitely presented over `R'`, then finitely many relations over `R` span, over
`R'`, the image in `F'` of every relation over `R`. -/
private theorem exists_fg_le_ker (hsurj : Function.Surjective (algebraMap Rₛ R'))
    (hι : IsBaseChange R' ι) [Module.Finite R' F'] [Module.FinitePresentation R' M']
    (φ : F →ₗ[R] M') (hspan : Submodule.span R' (LinearMap.range φ : Set M') = ⊤) :
    ∃ K : Submodule R F, K.FG ∧ K ≤ LinearMap.ker φ ∧
      ∀ c : F, φ c = 0 → ι c ∈ Submodule.span R' (ι '' K) := by
  obtain ⟨φ', hφ'⟩ : ∃ φ' : F' →ₗ[R'] M', ∀ c : F, φ' (ι c) = φ c := ⟨hι.lift φ, hι.lift_eq φ⟩
  have hφ'surj : Function.Surjective φ' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨ι c, hφ' c⟩
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.FinitePresentation.fg_ker φ' hφ'surj)
  have hkker : ∀ j, φ' (k j) = 0 := fun j =>
    LinearMap.mem_ker.mp (hk.le (Submodule.subset_span ⟨j, rfl⟩))
  choose s c hsc using fun j : Fin m => exists_smul_mem_range S Rₛ hsurj hι (k j)
  refine ⟨Submodule.span R (Set.range c), Submodule.fg_span (Set.finite_range c), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (by rw [← hφ', ← hsc j, map_smul, hkker j, smul_zero])
  · have hle : Submodule.span R' (Set.range k) ≤
        Submodule.span R' (ι '' Submodule.span R (Set.range c)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      obtain ⟨u, hu⟩ := isUnit_algebraMap S Rₛ (R' := R') (s j)
      rw [SetLike.mem_coe, show k j = ((u⁻¹ : R'ˣ) : R') • ι (c j) by
        rw [← hsc j, ← hu, smul_smul, u.inv_mul, one_smul]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨c j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩)
    exact fun z hz => hle (hk.ge (LinearMap.mem_ker.mpr (by rw [hφ', hz])))

end BaseChange

/-- **Stacks 05N5.** Let `R` be a ring, `S ⊆ R` a multiplicative subset, `Rₛ = S⁻¹R` and let
`R'` be a quotient of `Rₛ` (for instance `R' = S⁻¹(R/I) = Rₛ/I·Rₛ` for an ideal `I ⊆ R`). For
every finite `R'`-module `M'` there is a finite `R`-module `M` and an `R`-linear map
`g : M → M'` exhibiting `M'` as the base change `R' ⊗_R M`, i.e. as `S⁻¹(M/IM)`; and if `M'` is
finitely presented over `R'`, then `M` may be taken finitely presented over `R`. -/
@[stacks 05N5 "Stated for an arbitrary surjection `Rₛ → R'` from a localization `Rₛ = S⁻¹R`
in place of `R' = S⁻¹(R/I)`, of which it is the case `R' = Rₛ ⧸ I·Rₛ`; `S⁻¹(M/IM)` is the base
change `R' ⊗_R M`, pinned by `IsBaseChange R' g` for the source's map `g : M → M'`. Items (1)
and (2) are the two conjuncts."]
theorem exists_finite_isBaseChange_of_surjective_algebraMap {R : Type u} [CommRing R]
    (S : Submonoid R) (Rₛ : Type v) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra Rₛ R'] [IsScalarTower R Rₛ R']
    (M' : Type t) [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    [Module.Finite R' M'] (hsurj : Function.Surjective (algebraMap Rₛ R')) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M) (g : M →ₗ[R] M'),
      Module.Finite R M ∧ IsBaseChange R' g ∧
        (Module.FinitePresentation R' M' → Module.FinitePresentation R M) := by
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R') (M := M')
  obtain ⟨ι, hι⟩ : ∃ ι : (Fin n → R) →ₗ[R] (Fin n → R'), IsBaseChange R' ι :=
    ⟨_, IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R R')⟩
  obtain ⟨φ, hspan⟩ : ∃ φ : (Fin n → R) →ₗ[R] M',
      Submodule.span R' (LinearMap.range φ : Set M') = ⊤ :=
    ⟨Fintype.linearCombination R x, by
      rw [Fintype.range_linearCombination, Submodule.span_span_of_tower, hx]⟩
  obtain ⟨K, hKle, hKK, hKfg⟩ := exists_le_and_fg_of_imp (LinearMap.ker φ)
    (fun K => ∀ c, φ c = 0 → ι c ∈ Submodule.span R' (ι '' K)) (Module.FinitePresentation R' M')
    (fun z hz => Submodule.subset_span ⟨z, hz, rfl⟩) fun _ => exists_fg_le_ker S Rₛ hsurj hι φ hspan
  exact ⟨(Fin n → R) ⧸ K, inferInstance, inferInstance, K.liftQ φ hKle,
    Module.Finite.of_surjective K.mkQ K.mkQ_surjective,
    isBaseChange_liftQ S Rₛ hsurj hι φ hspan K hKle hKK,
    fun h => Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective
      (by simpa using hKfg h)⟩

end Module

/-- If the reduction `A/I → B/J` of a ring map `f` is injective, then `f⁻¹(J) ≤ I`; in
particular `Ker f ≤ I`. This is the converse of `Ideal.quotientMap_injective'`. -/
private theorem comap_le_of_quotientMap_injective {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} {f : A →+* B} {H : I ≤ J.comap f}
    (h : Function.Injective (Ideal.quotientMap J f H)) : J.comap f ≤ I := fun x hx =>
  Ideal.Quotient.eq_zero_iff_mem.1 <| h <| by
    rwa [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]

section AlgebraMaps

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {S' : Type*} [CommRing S']
  [Algebra R S] [Algebra R S']

/-- The kernel of a surjection `f : S → S'` of `R`-algebras is finitely generated as soon as `S`
is of finite type and `S'` of finite presentation over `R`. This is
`Algebra.FinitePresentation.ker_fG_of_surjective` with finite presentation of the source over `R`
weakened to finite type. -/
private theorem ker_fG_of_surjective_of_finiteType [Algebra.FiniteType R S]
    [Algebra.FinitePresentation R S'] (f : S →ₐ[R] S') (hf : Function.Surjective f) :
    (RingHom.ker (f : S →+* S')).FG := by
  have hfp : (f : S →+* S').FinitePresentation :=
    RingHom.FinitePresentation.of_comp_finiteType (algebraMap R S)
      (f.comp_algebraMap ▸ RingHom.finitePresentation_algebraMap.mpr ‹_›)
      (RingHom.finiteType_algebraMap.mpr ‹_›)
  let _ : Algebra S S' := (f : S →+* S').toAlgebra
  have _ : Algebra.FinitePresentation S S' := hfp
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hf

/-- If `S'` is flat over `R`, `f : S →ₐ[R] S'` is surjective and `Ker f ≤ IS`, then
`Ker f ≤ IS · Ker f`. -/
private theorem ker_le_map_smul_ker_of_flat [Module.Flat R S'] (I : Ideal R) (f : S →ₐ[R] S')
    (hf : Function.Surjective f) (h : RingHom.ker (f : S →+* S') ≤ I.map (algebraMap R S)) :
    RingHom.ker (f : S →+* S') ≤ I.map (algebraMap R S) • RingHom.ker (f : S →+* S') := by
  have hker : LinearMap.ker f.toLinearMap = (RingHom.ker (f : S →+* S')).restrictScalars R := by
    ext x
    simp [RingHom.mem_ker]
  change (RingHom.ker (f : S →+* S')).restrictScalars R ≤
    Submodule.restrictScalars R (I.map (algebraMap R S) • RingHom.ker (f : S →+* S'))
  rw [Ideal.smul_restrictScalars, ← hker,
    ← LinearMap.ker_inf_smul_top_eq_smul_of_flat I f.toLinearMap hf, hker, Ideal.smul_top_eq_map]
  exact le_inf le_rfl h

end AlgebraMaps

/-- **Stacks 07RE**. Let `I ⊆ R` be an ideal all of whose elements are nilpotent, let `S` be of
finite type over `R` and let `S'` be of finite presentation and flat over `R`. If an `R`-algebra
map `f : S →ₐ[R] S'` induces a bijection `S/IS → S'/IS'`, then `f` is bijective. -/
@[stacks 07RE "That `I` consists of nilpotents is spelled `I ≤ nilradical R`, the source's
`S/IS → S'/IS'` is `Ideal.quotientMapₐ` applied to `f`, and finite type, finite presentation and
flatness are instance arguments.", sga "1 III 4.2" "affine case + finiteness"]
theorem AlgHom.bijective_of_bijective_quotientMapₐ_of_le_nilradical
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] {S' : Type w} [CommRing S']
    [Algebra R S] [Algebra R S'] [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    [Module.Flat R S'] (I : Ideal R) (hI : I ≤ nilradical R) (f : S →ₐ[R] S')
    (hf : Function.Bijective
      (Ideal.quotientMapₐ (I.map (algebraMap R S')) f
          (Ideal.map_le_iff_le_comap.mpr fun x hx ↦
            show f (algebraMap R S x) ∈ I.map (algebraMap R S') from
              f.commutes x ▸ Ideal.mem_map_of_mem _ hx) :
        S ⧸ I.map (algebraMap R S) →ₐ[R] S' ⧸ I.map (algebraMap R S'))) :
    Function.Bijective f := by
  have hIS : I.map (algebraMap R S) ≤ (I.map (algebraMap R S')).comap (f : S →+* S') :=
    Ideal.map_le_iff_le_comap.mpr fun x hx =>
      show f (algebraMap R S x) ∈ I.map (algebraMap R S') from
        f.commutes x ▸ Ideal.mem_map_of_mem _ hx
  have hbij : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S')) (f : S →+* S') hIS) := hf
  have hsurj : Function.Surjective f :=
    surjective_of_surjective_mod_locallyNilpotent I
      (show I.IsLocallyNilpotent from fun _ hx => mem_nilradical.mp (hI hx)) f
      (Ideal.quotientMap_comp_mk hIS ▸ hbij.surjective.comp Ideal.Quotient.mk_surjective)
      inferInstance
  have hjac : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥ :=
    ((Ideal.map_mono hI).trans <| (Ideal.map_radical_le _).trans <| by simp).trans
      Ideal.radical_le_jacobson
  exact ⟨(RingHom.injective_iff_ker_eq_bot (f : S →+* S')).mpr
    (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      (ker_fG_of_surjective_of_finiteType f hsurj)
      (ker_le_map_smul_ker_of_flat I f hsurj
        ((Ideal.ker_le_comap _).trans (comap_le_of_quotientMap_injective hbij.injective))) hjac),
    hsurj⟩

end
