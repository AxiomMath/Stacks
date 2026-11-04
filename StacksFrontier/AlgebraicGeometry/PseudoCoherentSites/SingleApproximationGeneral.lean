module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SingleApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# Approximating a complex on a ringed site by a module placed in its top degree

Let `(C, O)` be a ringed site, let `𝒦` be a complex of `O`-modules whose cohomology vanishes
above a degree `p`, and suppose that every object `U` of `C` admits a covering family over each
member `V` of which there are a direct summand `𝒜` of a finite free `O|_V`-module together with
a map `𝒜 ⟶ Z^p(𝒦|_V)` whose composite with `Z^p(𝒦|_V) ⟶ H^p(𝒦|_V)` is an epimorphism. Then
`𝒦` is `p`-pseudo-coherent, the approximating strictly perfect complex being `𝒜` placed in
degree `p`.

This is the ringed-site form of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local_epi_homologyπ` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SingleApproximation.lean`. It is a restatement
and not a specialisation: the covering is a covering presieve rather than a point-indexed
family of opens, and the strict perfectness of the approximating complex is the `IsStrictlyPerfect`
of Stacks 08FL at the structure sheaf of the site rather than
`StrictlyPerfect.IsStrictlyPerfect` of a ringed space — the two agree where both are defined,
by `AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff`, but neither statement
instantiates the other inside Lean.

Everything that is not about the site is reused verbatim from the ringed-space file, which
states it for an arbitrary abelian category: `CochainComplex.homFromSingleOfCycles` is the
morphism `𝒜[-p] ⟶ 𝒦` determined by a map `𝒜 ⟶ Z^p(𝒦)`, and
`CochainComplex.epi_homologyMap_homFromSingleOfCycles` is its epimorphy on degree-`p`
cohomology.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_singleObj`: a direct summand of a finite free
  module, placed in a single degree, is a strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general`:
  the criterion for `p`-pseudo-coherence of a complex.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_local_epi_homologyπ_general`: the
  same for the object of `D(O)` the complex represents.

## Implementation notes

The only new input over the ringed-space proof is
`AlgebraicGeometry.RingedSite.isZero_homology_restrictComplex_general`, restriction to a slice
preserving the vanishing of a cohomology sheaf, in place of the ringed-space
`isZero_restrictComplex_homology`.

`AlgebraicGeometry.RingedSite.isDirectSummandOfFiniteFree_of_isZero` repeats, at a free module
universe, a `private` lemma of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`; that file is owned
elsewhere, so the lemma cannot be made public there.

The derived-category clause needs no transfer machinery: `IsPseudoCoherentFrom` asks for *some*
`p`-pseudo-coherent complex representing the object, and the complex at hand represents its own
image under the localisation functor.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section StrictlyPerfectSingle

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A zero sheaf of modules is a direct summand of the free module on the empty index type:
both maps out of and into a zero object are zero, and their composite is the identity.

This is a verbatim repetition of the `private`
`Stacks.SheafOfModules.isDirectSummandOfFiniteFree_of_isZero` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`, which is at the
same universes and has the same proof; that file is owned elsewhere, so the lemma cannot be
made public there and the repetition cannot be removed by an import. -/
theorem isDirectSummandOfFiniteFree_of_isZero {M : SheafOfModules.{w} R} (hM : IsZero M) :
    IsDirectSummandOfFiniteFree R M :=
  (isDirectSummandOfFiniteFree_iff_free R M).mpr ⟨0, 0, 0, hM.eq_of_src _ _⟩

/-- **A direct summand of a finite free module, placed in a single degree, is strictly
perfect.** Only one term is nonzero, so the boundedness condition holds; that term is the given
module up to the canonical isomorphism `HomologicalComplex.singleObjXSelf`, and every other
term vanishes. -/
theorem isStrictlyPerfect_singleObj {A : SheafOfModules.{w} R}
    (hA : IsDirectSummandOfFiniteFree R A) (p : ℤ) :
    IsStrictlyPerfect R
      ((HomologicalComplex.single (SheafOfModules.{w} R) (ComplexShape.up ℤ) p).obj A) where
  bounded := by
    refine (Set.finite_singleton p).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi
    by_contra hne
    exact hi (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) p A i
      (by simpa only [Set.mem_singleton_iff] using hne))
  termDirectSummand i := by
    by_cases hip : i = p
    · subst hip
      exact IsDirectSummandOfFiniteFree.of_iso R
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i A) hA
    · exact isDirectSummandOfFiniteFree_of_isZero R
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) p A i hip)

end StrictlyPerfectSingle

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A complex of `O`-modules with no cohomology above `p` which locally admits a map to its
degree-`p` cycles from a direct summand of a finite free module, epimorphic onto the degree-`p`
cohomology, is `p`-pseudo-coherent.**

The approximating strictly perfect complex is the given module placed in degree `p`
(`AlgebraicGeometry.RingedSite.isStrictlyPerfect_singleObj`) and the approximating morphism is
`CochainComplex.homFromSingleOfCycles`. Above degree `p` both complexes have vanishing
cohomology — the one because it is concentrated in degree `p`, the other by hypothesis and
because restriction to a slice is exact — so the map on cohomology there is a map between zero
objects; in degree `p` it is an epimorphism by
`CochainComplex.epi_homologyMap_homFromSingleOfCycles`. -/
theorem isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (L.homology j))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V),
          IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) A ∧
          ∃ c : A ⟶ (X.restrictComplex L V).cycles p,
            Epi (c ≫ (X.restrictComplex L V).homologyπ p)) :
    X.IsPseudoCoherentComplexFrom L p := by
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨A, hA, c, hc⟩ := hdata f hf
  refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj A,
    isStrictlyPerfect_singleObj ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) hA p,
    CochainComplex.homFromSingleOfCycles (X.restrictComplex L V) p c, fun j hj => ?_, ?_⟩
  · refine (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) p A j
      (by omega)).isIso ?_ _
    exact X.isZero_homology_restrictComplex_general V L j (hvanish j hj)
  · exact CochainComplex.epi_homologyMap_homFromSingleOfCycles _ p c hc

/-- The object of `D(O)` represented by a complex as in
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general` is
`p`-pseudo-coherent: that complex is itself a representative. -/
theorem isPseudoCoherentFrom_Q_of_local_epi_homologyπ_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (L.homology j))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V),
          IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) A ∧
          ∃ c : A ⟶ (X.restrictComplex L V).cycles p,
            Epi (c ≫ (X.restrictComplex L V).homologyπ p)) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj L) p :=
  ⟨L, isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general X L p hvanish h,
    ⟨Iso.refl _⟩⟩

end Main

end AlgebraicGeometry.RingedSite

end
