module

public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.LocalProperties.StandardCover

/-!
# Gluing dualizing complexes along a standard open cover

Let `A` be a Noetherian ring and let `f : ι → A` be a family of elements generating the unit
ideal. If the derived localization of `K ∈ D(A)` at every `f i` is a dualizing complex over
`A_{f i}`, then `K` is a dualizing complex over `A`. Each of the three defining conditions of a
dualizing complex is local on `Spec A`; this module establishes the two that are controlled by the
cohomology modules of `K`, namely boundedness and finiteness of the cohomology.

The family is indexed by an arbitrary type: membership of `1` in the span of the range of `f`
already involves only finitely many members, and `exists_finite_index_set_span_eq_top` extracts a
subfamily indexed by a finite set of indices, which is the form in which the source states the
hypothesis.

## Main results

* `Dualizing.isPseudoCoherent_of_localizations`: an object of `D(A)` whose derived localizations
  along a standard open cover are dualizing complexes is pseudo-coherent.
* `Dualizing.finite_homology_of_localizations`: consequently its cohomology modules are finite
  `A`-modules, which is condition (2) of [stacks 0A7B] for `K`.
* `Dualizing.isGE_and_isLE_of_localizations`: such an object is bounded.
* `Dualizing.isZero_homology_of_localizations`: vanishing of a cohomology module is local on a
  standard open cover.

## Implementation notes

The derived localization is `StacksDraft.PseudoCoherence.localizationAwayFunctorAux`, the derived
functor of termwise extension of scalars along `A → A_f`; extension of scalars along a
localization is exact, so no derived correction is needed and the functor commutes with the
cohomology functors of the derived category by
`StacksDraft.PseudoCoherence.localizationAwayHomologyIso`. Finiteness of the cohomology is not
proved degree by degree: pseudo-coherence descends along a standard open cover ([stacks 066D],
available as
`StacksDraft.PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux`), and
over a Noetherian ring pseudo-coherence is exactly boundedness above together with finiteness of
all the cohomology modules ([stacks 066E]).

## References

* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Dualizing

/-- The cohomology of a derived object of injective amplitude in `[a, b]` vanishes outside
`[a, b]`. -/
theorem isZero_homology_of_hasInjectiveAmplitude {A : Type u} [CommRing A]
    {K : DerivedCategory (ModuleCat.{u} A)} {a b : ℤ}
    (h : StacksDraft.InjectiveDimension.HasInjectiveAmplitude K a b) (n : ℤ)
    (hn : n < a ∨ b < n) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) := by
  obtain ⟨I, hGE, hLE, -, ⟨e⟩⟩ := h
  have := hGE
  have := hLE
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso e)
  rcases hn with hn | hn
  · exact DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj I) a n hn
  · exact DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj I) b n hn

section Cover

variable {A : Type u} [CommRing A] {ι : Type w} (f : ι → A)

/-- A family of elements generating the unit ideal has a subfamily, indexed by a finite set of
indices, which still generates the unit ideal. -/
theorem exists_finite_index_set_span_eq_top (hspan : Ideal.span (Set.range f) = ⊤) :
    ∃ s : Set ι, s.Finite ∧ Ideal.span (Set.range fun i : s => f i.1) = ⊤ := by
  classical
  obtain ⟨t, hsub, htop⟩ := (Ideal.span_eq_top_iff_finite (Set.range f)).mp hspan
  have hchoice : ∀ x : (t : Set A), ∃ i : ι, f i = x.1 := fun x => hsub x.2
  choose idx hidx using hchoice
  refine ⟨Set.range idx, Set.finite_range idx, top_unique ?_⟩
  rw [← htop]
  exact Ideal.span_mono fun x hx => ⟨⟨idx ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hidx ⟨x, hx⟩⟩

/-- **Stacks 00EO (1) for derived cohomology.** The cohomology of a derived object vanishes in a
degree as soon as the cohomology of all its derived localizations along a family generating the
unit ideal vanishes there. -/
theorem isZero_homology_of_localizations (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : ∀ i, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (f i))) n).obj
        ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} (f i)).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine Module.subsingleton_of_localizationSpan_range f hspan fun i => ?_
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((h i).of_iso
      (StacksDraft.PseudoCoherence.localizationAwayHomologyIso.{u, u} (f i) K n).symm)

variable [IsNoetherianRing A]

/-- A dualizing complex is pseudo-coherent: it is bounded above, because it is represented by a
bounded complex of injectives, and its cohomology modules are finite. -/
theorem isPseudoCoherent_of_isDualizingComplex
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
  obtain ⟨a, b, hamp⟩ := hK.finiteInjectiveDimension
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    K 0 A).2.1.mpr
    ⟨⟨b, fun n hn => isZero_homology_of_hasInjectiveAmplitude hamp n (Or.inr hn)⟩,
      hK.finiteCohomology⟩

/-- If the derived localization of `K` at every member of a family generating the unit ideal is a
dualizing complex, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_localizations (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex
      ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} (f i)).obj K)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K := by
  obtain ⟨s, hsfin, hspan'⟩ := exists_finite_index_set_span_eq_top f hspan
  have : Finite s := hsfin
  refine (StacksDraft.PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux
    (fun i : s => f i.1) hspan' K 0).2 fun i => ?_
  exact isPseudoCoherent_of_isDualizingComplex _ (hK i.1)

/-- **Finiteness of the cohomology glues**, condition (2) of [stacks 0A7B] in [stacks 0A7H]. If
the derived localization of `K` at every member of a family generating the unit ideal is a
dualizing complex, then every cohomology module of `K` is a finite `A`-module. -/
theorem finite_homology_of_localizations (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex
      ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} (f i)).obj K))
    (n : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) :=
  ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology K 0 A).2.1.mp
    (isPseudoCoherent_of_localizations f hspan K hK)).2 n

/-- **Boundedness glues.** If the derived localization of `K` at every member of a family
generating the unit ideal is a dualizing complex, then `K` is bounded: the injective amplitudes of
the localizations of the finite subfamily extracted from the cover have a common window. -/
theorem isGE_and_isLE_of_localizations (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i, IsDualizingComplex
      ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} (f i)).obj K)) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  classical
  obtain ⟨s, hsfin, hspan'⟩ := exists_finite_index_set_span_eq_top f hspan
  have : Finite s := hsfin
  choose a b hab using fun i : s => (hK i.1).finiteInjectiveDimension
  obtain ⟨a', ha'⟩ := Finite.bddBelow_range a
  obtain ⟨b', hb'⟩ := Finite.bddAbove_range b
  refine ⟨a', b', (DerivedCategory.isGE_iff K a').2 fun n hn => ?_,
    (DerivedCategory.isLE_iff K b').2 fun n hn => ?_⟩
  · refine isZero_homology_of_localizations (fun i : s => f i.1) hspan' K n fun i => ?_
    exact isZero_homology_of_hasInjectiveAmplitude (hab i) n
      (Or.inl (lt_of_lt_of_le hn (ha' ⟨i, rfl⟩)))
  · refine isZero_homology_of_localizations (fun i : s => f i.1) hspan' K n fun i => ?_
    exact isZero_homology_of_hasInjectiveAmplitude (hab i) n
      (Or.inr (lt_of_le_of_lt (hb' ⟨i, rfl⟩) hn))

end Cover

end Dualizing
