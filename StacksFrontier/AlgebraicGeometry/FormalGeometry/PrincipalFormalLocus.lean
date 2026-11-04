module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivityClosed
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComplementFormalFunctions
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# The formal locus of a principal ideal, and the comparison map there

Let `𝔞` be an ideal of a commutative ring `A`, let `f ∈ A` and let `U = Spec(A) ∖ V(𝔞)`. The
formal locus of the principal ideal `(f)` inside `U` is `U ∩ V(f)`, the set of points of `U`
whose prime contains `f`, and the neighbourhoods of it are the opens `V ⊆ U` with
`U ∩ V(f) ⊆ V`. They are the index category
`Stacks.Algebraization.OpensNearVanishing A (Ideal.span {f}) 𝔞`, whose defining condition is
stated for a general ideal as `I ≤ 𝔭`; for `I = (f)` that condition is `f ∈ 𝔭`, which is the
form in which the source writes it and the form in which a consumer discharges it.

This file records that translation, names the comparison map
`Stacks.Algebraization.comparisonMap` of a module of the shape `M̃|_U` at a principal formal
locus, and reduces its being an isomorphism to surjectivity alone.

The reduction has two halves. Injectivity is already available: it is
`Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing`, whose
hypothesis is that the closure of every associated point of the module meets the formal locus.
Surjectivity is not, and this file does not supply it; what it supplies is the statement of
surjectivity in the form the source's arguments produce it, namely that every compatible family
of sections of `F / fⁿ F` on `U` is the comparison of a single honest section of `F` on a single
neighbourhood of the formal locus. That the two agree is `IsFiltered` on the index category: a
class in the colimit is a section on one neighbourhood, so a surjection onto the limit is
exactly the realization of each formal section on one neighbourhood.

## Main definitions

* `Stacks.Algebraization.OpensNearVanishing.ofSpanSingleton` — a neighbourhood of a principal
  formal locus, built from the condition `f ∈ 𝔭`.
* `Stacks.Algebraization.principalComparisonMap` — the comparison map at the formal locus of
  `(f)`, for the restriction to `U` of the sheaf associated to an `A`-module.

## Main results

* `Stacks.Algebraization.contains_vanishing_span_singleton_iff` — for a principal ideal the
  defining condition of `OpensNearVanishing` is membership of `f` in the prime.
* `Stacks.Algebraization.surjective_comparisonMap_iff` — the comparison map is surjective
  exactly when every formal section is realized by a section on a single neighbourhood of the
  formal locus.
* `Stacks.Algebraization.isIso_comparisonMap_of_associatedPoints_of_realized` — the comparison
  map is an isomorphism as soon as the closure of every associated point meets the formal locus
  and every formal section is so realized.
* `Stacks.Algebraization.isIso_principalComparisonMap_of_associatedPoints_of_realized` — the
  same at a principal formal locus.

## Implementation notes

`Stacks.LocalCohomology.complementTilde A 𝔞 M` has declared type
`SheafOfModules (complementZeroLocus A 𝔞 : Scheme).ringCatSheaf`, while
`Stacks.Algebraization.comparisonMap` consumes a `(complementZeroLocus A 𝔞 : Scheme).Modules`.
The two are the same type once the module universe equals the universe of `A`, so
`principalComparisonMap` is stated with a single universe; it is not stated with an independent
module universe, because `comparisonMap` is not.

The realization statement is phrased with `Stacks.Algebraization.comparisonAt`, the comparison
at a single neighbourhood, rather than with the colimit inclusion followed by the comparison
map. The two are equal by `Stacks.Algebraization.colimit_ι_comp_comparisonMap`, and the former
is the shape that mentions no colimit, which is what makes it the hypothesis a geometric
argument discharges.

Surjectivity is taken on the underlying map of abelian groups rather than as `Epi`: the target
is a limit in `Ab`, where an epimorphism is a surjection, and the concrete form is the one both
the hypothesis and `CategoryTheory.ConcreteCategory.isIso_iff_bijective` are stated in.

### Stacks 0EIH

Stacks 0EIH asserts, for `A` Noetherian, `f ∈ 𝔞`, `M` a finite `A`-module with `A`
`f`-adically complete, `f` a nonzerodivisor on `M` and `H¹_𝔞(M/fM)` a finite `A`-module, that
`principalComparisonMap A f 𝔞 M` is an isomorphism. Its map is exactly
`principalComparisonMap A f 𝔞 M`, defined here.

The **injectivity** half is proved, and unconditionally, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PrincipalFormalLocusTagInjectivity.lean`:
`Stacks.Algebraization.mono_principalComparisonMap`, carrying
`@[stacks 0EIH "injectivity"]`, needs only that `A` is Noetherian and `M` finite — none of
`f`-adic completeness, `f` a nonzerodivisor, finiteness of `H¹_𝔞(M/fM)`, or `f ∈ 𝔞`. The whole
statement is `Stacks.Algebraization.FormalSections.isIso_formalComparison` for the explicitly
constructed comparison map of locally fractional sections, and
`Stacks.Algebraization.isIso_comparisonMap_principalTilde` for the map defined here.

The injectivity half needs no associated-point hypothesis, such as the one of
`isIso_principalComparisonMap_of_associatedPoints_of_realized`: the hypothesis is unnecessary, and it is not even available under 0EIH's own
hypotheses — take `𝔞 = (f)`, so that `U ∩ V(f) = ∅` and no associated point of a nonzero
`M̃|_U` specializes into the formal locus. Injectivity of a colimit over *shrinking*
neighbourhoods never needed a section to vanish on the neighbourhood it started on: the locus
where a germ vanishes is open for any sheaf, it contains the formal locus by
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`, and the section restricts
to zero there. That argument also strictly strengthens
`Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing`, the
injectivity half of Stacks 0EG2, whose associated-point hypothesis can be retired.

## References

* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### The formal locus of a principal ideal -/

/-- For a principal ideal the defining condition of `Stacks.Algebraization.OpensNearVanishing`
is membership of the generator in the prime: an open of `U = Spec(A) ∖ V(𝔞)` contains every
point of `U` whose prime contains `(f)` exactly when it contains every point of `U` whose prime
contains `f`. -/
theorem contains_vanishing_span_singleton_iff (A : Type u) [CommRing A] (a : Ideal A) (f : A)
    (W : (complementZeroLocus A a : Scheme).Opens) :
    (∀ x : (complementZeroLocus A a : Scheme), Ideal.span {f} ≤ x.1.asIdeal → x ∈ W) ↔
      ∀ x : (complementZeroLocus A a : Scheme), f ∈ x.1.asIdeal → x ∈ W := by
  simp only [Ideal.span_singleton_le_iff_mem]

/-- A neighbourhood of the formal locus of a principal ideal, built from an open of
`U = Spec(A) ∖ V(𝔞)` containing every point of `U` at which `f` vanishes. -/
def OpensNearVanishing.ofSpanSingleton {A : Type u} [CommRing A] {a : Ideal A} (f : A)
    (W : (complementZeroLocus A a : Scheme).Opens)
    (hW : ∀ x : (complementZeroLocus A a : Scheme), f ∈ x.1.asIdeal → x ∈ W) :
    OpensNearVanishing A (Ideal.span {f}) a where
  openSet := W
  contains_vanishing := (contains_vanishing_span_singleton_iff A a f W).2 hW

/-- The open set of `Stacks.Algebraization.OpensNearVanishing.ofSpanSingleton f W hW` is `W`. -/
@[simp]
theorem OpensNearVanishing.ofSpanSingleton_openSet {A : Type u} [CommRing A] {a : Ideal A}
    (f : A) (W : (complementZeroLocus A a : Scheme).Opens)
    (hW : ∀ x : (complementZeroLocus A a : Scheme), f ∈ x.1.asIdeal → x ∈ W) :
    (OpensNearVanishing.ofSpanSingleton f W hW).openSet = W :=
  rfl

/-! ### Surjectivity of the comparison map, as realization on one neighbourhood -/

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- **The comparison map is surjective exactly when every formal section is realized on one
neighbourhood of the formal locus.** A compatible family of sections of `F / Iⁿ F` on all of `U`
is in the image of `Stacks.Algebraization.comparisonMap` precisely when it is the comparison of
an honest section of `F` over a single open `V ⊆ U` containing `U ∩ V(I)`. -/
theorem surjective_comparisonMap_iff :
    Function.Surjective (ConcreteCategory.hom (comparisonMap A I a F)) ↔
      ∀ s : ToType (limit (formalSections A I a F)),
        ∃ (V : OpensNearVanishing A I a) (t : ToType ((sectionsNearVanishing A I a F).obj V)),
          ConcreteCategory.hom (comparisonAt A I a F V) t = s := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  refine ⟨fun hsurj s => ?_, fun hreal s => ?_⟩
  · obtain ⟨z, hz⟩ := hsurj s
    obtain ⟨V, t, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
    refine ⟨V, t, ?_⟩
    rwa [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap] at hz
  · obtain ⟨V, t, ht⟩ := hreal s
    refine ⟨ConcreteCategory.hom (colimit.ι (sectionsNearVanishing A I a F) V) t, ?_⟩
    rwa [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap]

/-- **The comparison map is an isomorphism as soon as its two halves hold.** If the closure of
every associated point of `F` meets the formal locus `U ∩ V(I)`, and every compatible family of
sections of `F / Iⁿ F` on `U` is the comparison of a section of `F` on a single neighbourhood of
that locus, then the comparison map is an isomorphism.

The first hypothesis gives injectivity, by
`Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing`; the second
gives surjectivity, by `Stacks.Algebraization.surjective_comparisonMap_iff`; and a bijective
morphism of abelian groups is an isomorphism. -/
theorem isIso_comparisonMap_of_associatedPoints_of_realized [IsNoetherianRing A] [F.IsCoherent]
    (hAss : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ∃ y : (complementZeroLocus A a : Scheme), x ⤳ y ∧ I ≤ y.1.asIdeal)
    (hreal : ∀ s : ToType (limit (formalSections A I a F)),
      ∃ (V : OpensNearVanishing A I a) (t : ToType ((sectionsNearVanishing A I a F).obj V)),
        ConcreteCategory.hom (comparisonAt A I a F V) t = s) :
    IsIso (comparisonMap A I a F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
      (mono_comparisonMap_of_associatedPoints_specializes_vanishing A I a F hAss),
    (surjective_comparisonMap_iff A I a F).2 hreal⟩

/-! ### The comparison map at a principal formal locus -/

/-- **The comparison map of Stacks 0EIH.** For an `A`-module `M` and an element `f ∈ A`, the
canonical map from the sections of `M̃` on the opens `V ⊆ U = Spec(A) ∖ V(𝔞)` containing
`U ∩ V(f)` to the compatible families of sections on all of `U` of the quotients of `M̃|_U` by
the powers of `f`. -/
def principalComparisonMap (A : Type u) [CommRing A] (f : A) (a : Ideal A)
    (M : ModuleCat.{u} A) :
    colimit (sectionsNearVanishing A (Ideal.span {f}) a (complementTilde A a M)) ⟶
      limit (formalSections A (Ideal.span {f}) a (complementTilde A a M)) :=
  comparisonMap A (Ideal.span {f}) a (complementTilde A a M)

/-- The comparison map at a principal formal locus is an isomorphism as soon as the closure of
every associated point of `M̃|_U` contains a point of `U` at which `f` vanishes, and every
compatible family of sections of the quotients by the powers of `f` is realized by a section of
`M̃` on a single open `V ⊆ U` containing `U ∩ V(f)`. -/
theorem isIso_principalComparisonMap_of_associatedPoints_of_realized (A : Type u) [CommRing A]
    [IsNoetherianRing A] (f : A) (a : Ideal A) (M : ModuleCat.{u} A)
    [(complementTilde A a M).IsCoherent]
    (hAss : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints (complementTilde A a M) →
      ∃ y : (complementZeroLocus A a : Scheme), x ⤳ y ∧ f ∈ y.1.asIdeal)
    (hreal : ∀ s : ToType (limit (formalSections A (Ideal.span {f}) a (complementTilde A a M))),
      ∃ (V : OpensNearVanishing A (Ideal.span {f}) a)
        (t : ToType ((sectionsNearVanishing A (Ideal.span {f}) a
          (complementTilde A a M)).obj V)),
        ConcreteCategory.hom
          (comparisonAt A (Ideal.span {f}) a (complementTilde A a M) V) t = s) :
    IsIso (principalComparisonMap A f a M) :=
  isIso_comparisonMap_of_associatedPoints_of_realized A (Ideal.span {f}) a
    (complementTilde A a M)
    (fun x hx => (hAss x hx).imp fun _ h => ⟨h.1, (Ideal.span_singleton_le_iff_mem _).2 h.2⟩)
    hreal

end Stacks.Algebraization

/-! ### The comparison at a single power

The companion statement in which the colimit over neighbourhoods is replaced by the sections on
`U` itself is already proved, for a finite module over a Noetherian ring complete at `(f)` whose
first two local cohomology modules are annihilated by a power of `f`. Its hypotheses are those of
the source, with the membership `f ∈ 𝔞` carried but unused, so the statement there is the more
general one. -/

add_to_stacks 0EII Stacks.Algebraization.ComplementTower.sectionsToLimit_isIso

end
