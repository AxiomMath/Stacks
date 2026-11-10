module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Locus
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs

/-!
# Essentially smooth ring maps

A ring map is *essentially smooth* when it is essentially of finite presentation (Tag 00QM (2))
and formally smooth. This is the localized form of smoothness: a smooth ring map is one that is
of finite presentation and formally smooth (Definition 00T2, by Proposition 00TN), and allowing
the finitely presented algebra to be localized gives the class that the local arguments of the
Smoothing Ring Maps chapter work with.

## Main definitions

* `RingHom.IsEssentiallySmooth`: a ring map essentially of finite presentation whose target is
  formally smooth over its source.

## Main results

* `IsEssentiallyOfFinitePresentation.of_isLocalization`: a localization of an algebra of finite
  presentation is essentially of finite presentation.
* `RingHom.IsEssentiallySmooth.of_etale`: an étale ring map is essentially smooth.
* `RingHom.IsEssentiallySmooth.of_isEtaleAt`: if `S` is of finite presentation over `R` and `R`
  is étale at a prime `q` of `S`, then `R → S_q` is essentially smooth.
* `RingHom.IsEssentiallySmooth.comp_ringEquiv`: essential smoothness travels along an
  isomorphism of the target.

## Implementation notes

The Stacks Project uses the term "essentially smooth" in Lemma 07FH and in the two lemmas
following it without ever defining it, so no declaration here carries a Stacks tag. The
definition taken is the one those proofs need: they produce an étale ring map and conclude
essential smoothness from it, which is the implication `of_etale` below.

`Algebra.IsEtaleAt R q` is formal étaleness of the local ring `Localization.AtPrime q`, so
`of_isEtaleAt` is the form in which `Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal` (Tag 00U6)
produces essential smoothness, and `comp_ringEquiv` carries that conclusion to any other model of
the local ring.

Essential finite presentation is the single-universe predicate
`IsEssentiallyOfFinitePresentation` of Tag 00QM (2), which forces source and target into one
universe; `RingHom.EssentiallyOfFinitePresentation` is the universe-polymorphic variant of the
same notion and is not used here.

## References

* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
* [Stacks Project, Tag 00QM](https://stacks.math.columbia.edu/tag/00QM)
* [Stacks Project, Tag 00U6](https://stacks.math.columbia.edu/tag/00U6)
-/

@[expose] public section

universe u

/-- A localization of an algebra of finite presentation is essentially of finite presentation
over the base. -/
theorem IsEssentiallyOfFinitePresentation.of_isLocalization {R C S : Type u} [CommRing R]
    [CommRing C] [CommRing S] [Algebra R C] [Algebra C S] [Algebra R S] [IsScalarTower R C S]
    [Algebra.FinitePresentation R C] (U : Submonoid C) [IsLocalization U S] :
    IsEssentiallyOfFinitePresentation R S (algebraMap R S) := by
  unfold IsEssentiallyOfFinitePresentation
  rw [toAlgebra_algebraMap]
  exact ⟨C, inferInstance, inferInstance, inferInstance, U, inferInstance, inferInstance,
    inferInstance⟩

/-- A ring map is *essentially smooth* if it is essentially of finite presentation and its target
is formally smooth over its source. -/
def RingHom.IsEssentiallySmooth {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  IsEssentiallyOfFinitePresentation R S f ∧ Algebra.FormallySmooth R S

/-- An étale ring map is essentially smooth: it is of finite presentation, hence essentially of
finite presentation, and formally étale, hence formally smooth. -/
theorem RingHom.IsEssentiallySmooth.of_etale {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : (algebraMap R S).IsEssentiallySmooth := by
  have : IsLocalization (⊥ : Submonoid S) S := IsLocalization.self (by simp)
  refine ⟨IsEssentiallyOfFinitePresentation.of_isLocalization (C := S) ⊥, ?_⟩
  rw [toAlgebra_algebraMap]
  infer_instance

/-- If `S` is of finite presentation over `R` and `R → S` is étale at a prime `q` of `S`, then
the map `R → S_q` to the local ring at `q` is essentially smooth. -/
theorem RingHom.IsEssentiallySmooth.of_isEtaleAt {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Algebra.IsEtaleAt R q] :
    (algebraMap R (Localization.AtPrime q)).IsEssentiallySmooth := by
  refine ⟨IsEssentiallyOfFinitePresentation.of_isLocalization (C := S) q.primeCompl, ?_⟩
  rw [toAlgebra_algebraMap]
  infer_instance

/-- Composing an essentially smooth ring map with an isomorphism of its target gives an
essentially smooth ring map. -/
theorem RingHom.IsEssentiallySmooth.comp_ringEquiv {R S S' : Type u} [CommRing R] [CommRing S]
    [CommRing S'] {f : R →+* S} (hf : f.IsEssentiallySmooth) (e : S ≃+* S') :
    ((e : S →+* S').comp f).IsEssentiallySmooth := by
  let := f.toAlgebra
  let := ((e : S →+* S').comp f).toAlgebra
  obtain ⟨⟨T, _, _, _, M, _, htow, hloc⟩, hsm⟩ := hf
  let : Algebra T S' := ((e : S →+* S').comp (algebraMap T S)).toAlgebra
  have htow' : IsScalarTower R T S' := IsScalarTower.of_algebraMap_eq' <| by
    change (e : S →+* S').comp f = ((e : S →+* S').comp (algebraMap T S)).comp (algebraMap R T)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R T S]
    rfl
  have hloc' : IsLocalization M S' := (IsLocalization.isLocalization_iff_of_ringEquiv M e).mp hloc
  have he : ∀ r : R, e (algebraMap R S r) = algebraMap R S' r := fun _ => rfl
  exact ⟨⟨T, inferInstance, inferInstance, inferInstance, M, inferInstance, htow', hloc'⟩,
    Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv he)⟩
