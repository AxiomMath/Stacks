module

public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

import StacksFrontier.RingTheory.Norm.Projective

/-!
# An invertible module is exactly a finite locally free module of rank one

Let `R` be a commutative ring and `M` an `R`-module. This file proves

`Module.IsFiniteLocallyFreeOfRank R M 1 ↔ Module.Invertible R M`,

that is, `M` is invertible exactly when there is a family of elements of `R` generating the unit
ideal such that each localization of `M` away from one of them has a basis indexed by `Fin 1`.

## Main results

* `Module.invertible_of_isFiniteLocallyFreeOfRank_one`: finite locally free of rank one implies
  invertible.
* `Module.isFiniteLocallyFreeOfRank_one_of_invertible`: invertible implies finite locally free of
  rank one.
* `Module.isFiniteLocallyFreeOfRank_one_iff_invertible`: the two together.

## Why this is here

This is one of the two links missing from the chain that identifies an **invertible module sheaf
on `Spec R` with an invertible `R`-module** — a gap recorded as outstanding in two places, both
of which are steps of Stacks Tag 0C0T's elementary route:

* `StacksFrontier/AlgebraicGeometry/SemilocalFibre/Basic.lean` records that "nothing
  identifies an invertible module sheaf on `Spec R` with an invertible `R`-module, so the
  invertible `𝒪_X`-module of the tag cannot yet be fed to the statements below";
* `StacksFrontier/AlgebraicGeometry/SpreadingOut/Basic.lean` records the same absence as
  the reason it takes the one-point-fibre branch of the step instead of the semilocal one.

Pinned Mathlib records the same gap as a `TODO` in `Mathlib/RingTheory/PicardGroup.lean`:
"Establish other characterizations of invertible modules, e.g. they are modules that become free
of rank one when localized at every prime ideal" and "Connect to invertible sheaves on `Spec R`."

The absence is of the *statement*, not of the mathematics: in Mathlib and in this library no
declaration mentions both `Module.Invertible`/`CommRing.Pic` and any locally-free-of-rank-one
predicate, while the rest of the chain is available. What is needed is a composition, in both
directions:

* **invertible ⟹ locally free of rank one** is `Module.Invertible.exists_finset_free_localization`
  (pinned Mathlib) — which gives *freeness* of each localization but not the *rank* — together
  with the instance `Module.Invertible (Localization S) (LocalizedModule S M)` and
  `Module.Invertible.free_iff_linearEquiv`, which upgrades "free" to "isomorphic to the ring" and
  hence to a basis indexed by `Fin 1`. The rank is the part Mathlib's lemma does not state.
* **locally free of rank one ⟹ invertible** is condition (6) ⟹ (2) of
  `Module.finite_projective_tfae` (Tag 00NX, in this library) to get finiteness and
  projectivity, plus `Module.rankAtStalk` identically one, fed to clause (1) ⟹ (2) of
  `Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse` (Tag 0B8I,
  also in this library).

## The remaining link, stated precisely

With this file in place, the chain from an invertible module sheaf on `Spec R` to an invertible
`R`-module has exactly **one** link left, and it is a spelling bridge rather than mathematics:

> `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank M r ↔
>  SheafOfModules.IsFiniteLocallyFreeOfRank M r`

the rank-`r` twin of `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`
(`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/Sheaf.lean`, which is stated only without a
rank). The two classes it compares are the one the invertibility results are stated over
(`Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one`) and the
one `AlgebraicGeometry.tilde_isFiniteLocallyFreeOfRank_iff` is stated over. The rank-`r`
transport exists today only as a `private`, one-directional lemma
(`moduleSpecΓ_isFiniteLocallyFreeOfRank` in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFreeNorm/Basic.lean`), so it cannot be used from
outside that file.

## Implementation notes

The rank of a finite locally free module, used below to feed clause (1) of Tag 0B8I, is
`Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank` from
`StacksFrontier/RingTheory/Norm/Projective.lean`, imported here. This file used to restate and
reprove it, having found only the `private` copy
(`module_rankAtStalk_eq_of_isFiniteLocallyFreeOfRank`, in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFreeNorm/Basic.lean`) that is unreachable by name
from another module; the dedup row it recorded against that copy is discharged by using the
public one instead.

No `stacks` attribute is attached. Tag 0C0T carries a single unlabelled assertion, so its
covering set is the whole statement and no partial-credit path exists; and the statements below
are commutative algebra that the tag does not assert. Tags 00NX and 0B8I are consumed, not
claimed.

## References

* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 0B8I](https://stacks.math.columbia.edu/tag/0B8I)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

universe u

namespace Module

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Finiteness and flatness from a finite locally free presentation -/

/-- A finite locally free module has a set of elements generating the unit ideal, each of whose
localizations has a finite basis. -/
private theorem exists_span_eq_top_nonempty_basis_away {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, Nonempty (Basis (Fin d) (Localization.Away g) (LocalizedModule.Away g M)) := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine ⟨Set.range f, by simpa using hspan, ?_⟩
  rintro g ⟨i, rfl⟩
  exact hbasis i

/-- A finite locally free module is finite: finiteness of a module is local on the base, and each
localization has a finite basis. -/
theorem finite_of_isFiniteLocallyFreeOfRank {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) : Module.Finite R M := by
  obtain ⟨s, hs, hbasis⟩ := exists_span_eq_top_nonempty_basis_away h
  refine Module.Finite.of_localizationSpan s hs ?_
  rintro ⟨g, hg⟩
  exact Module.Finite.of_basis (hbasis g hg).some

/-- A finite locally free module is flat: flatness is local on the base, a module with a basis is
free hence flat, and flatness composes along `R → R_{f}`. -/
theorem flat_of_isFiniteLocallyFreeOfRank {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) : Module.Flat R M := by
  obtain ⟨s, hs, hbasis⟩ := exists_span_eq_top_nonempty_basis_away h
  refine Module.flat_of_localized_span R M s hs ?_
  rintro ⟨g, hg⟩
  let : Module.Free (Localization.Away g) (LocalizedModule.Away g M) :=
    Module.Free.of_basis (hbasis g hg).some
  exact Module.Flat.trans R (Localization.Away g) _

/-! ### The two implications -/

/-- **A finite locally free module of rank one is invertible.** Finiteness and projectivity are
clause (6) ⟹ (2) of Tag 00NX, and the rank function is identically one by
`Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank`; those three facts are clause (1) of
Tag 0B8I, whose clause (2) is invertibility. -/
theorem invertible_of_isFiniteLocallyFreeOfRank_one
    (h : Module.IsFiniteLocallyFreeOfRank R M 1) : Module.Invertible R M := by
  have h6 : Module.Finite R M ∧ ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, Module.Free (Localization.Away g) (LocalizedModule.Away g M) := by
    obtain ⟨s, hs, hbasis⟩ := exists_span_eq_top_nonempty_basis_away h
    exact ⟨finite_of_isFiniteLocallyFreeOfRank h, s, hs,
      fun g hg ↦ Module.Free.of_basis (hbasis g hg).some⟩
  obtain ⟨hfin, hproj⟩ := ((Module.finite_projective_tfae R M).out 6 2).mp h6
  let : Module.Finite R M := hfin
  let : Module.Projective R M := hproj
  have hrank : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1 := by
    funext p
    exact rankAtStalk_eq_of_isFiniteLocallyFreeOfRank 1 h p
  have key := (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u,
    u, u} R M).1.out 1 2
  exact key.mp ⟨hfin, hproj, hrank⟩

/-- **An invertible module is finite locally free of rank one.** Mathlib's
`Module.Invertible.exists_finset_free_localization` supplies a finite family of elements
generating the unit ideal with each localization *free*; the localization of an invertible module
is invertible, and an invertible free module is isomorphic to the ring
(`Module.Invertible.free_iff_linearEquiv`), which turns each of those localizations into one with
a basis indexed by `Fin 1`. The rank is what the Mathlib lemma does not state. -/
theorem isFiniteLocallyFreeOfRank_one_of_invertible [Module.Invertible R M] :
    Module.IsFiniteLocallyFreeOfRank R M 1 := by
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization (R := R) (M := M)
  refine ⟨{x : R // x ∈ s}, fun x ↦ (x : R), by simpa [Subtype.range_coe] using hs, fun x ↦ ?_⟩
  let : Module.Free (Localization.Away (x : R))
      (LocalizedModule (Submonoid.powers (x : R)) M) := hfree (x : R) x.2
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv
    (R := Localization.Away (x : R))
    (M := LocalizedModule (Submonoid.powers (x : R)) M) |>.mp inferInstance
  exact ⟨(Basis.singleton (Fin 1) (Localization.Away (x : R))).map e.symm⟩

/-- **An `R`-module is invertible exactly when it is finite locally free of rank one.** This is
the characterization Mathlib's `PicardGroup` file records as a `TODO` and the one Tag 0C0T's
route needs in order to pass between an invertible module sheaf on `Spec R` and an invertible
`R`-module. -/
theorem isFiniteLocallyFreeOfRank_one_iff_invertible :
    Module.IsFiniteLocallyFreeOfRank R M 1 ↔ Module.Invertible R M :=
  ⟨invertible_of_isFiniteLocallyFreeOfRank_one,
    fun h ↦ let := h; isFiniteLocallyFreeOfRank_one_of_invertible⟩

end Module

end
