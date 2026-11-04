module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# A perfect complex is pseudo-coherent, at independent universes

This file is the universe-general form of the pseudo-coherence half of the implication
(1) ⟹ (2) of Stacks 08G8, which
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PseudoCoherenceAndTorAmplitude.lean` states
for a ringed site `X : RingedSite.{u, v, 0}` with modules in `SheafOfModules.{0}`.  Here it is
stated for `X : RingedSite.{u, v, w}` with modules in `SheafOfModules.{w}`, which is the shape
the small étale ringed site of a scheme over `Scheme.{u}` has: it is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, its objects lying strictly above its morphisms and
its sections.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isPerfectComplex_general`: a
  perfect complex of `O`-modules is `m`-pseudo-coherent, for every `m`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general`: a perfect object of
  `D(O)` is `m`-pseudo-coherent, for every `m`.

## Implementation notes

**Why this file exists rather than a generalization in place.**  The same reason as for
`StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/RestrictionGeneral.lean`: the source file is
owned by another development, and its two statements are restated here with `0` replaced by `w`
and no change to either proof.  The restatement is possible because both predicates are already
universe-general — `AlgebraicGeometry.RingedSite.IsPerfectComplex` and
`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` are stated at a ringed site
`RingedSite.{u, v, w}` with the module universe a further free parameter — and because the
argument is formal: a quasi-isomorphism is an isomorphism on cohomology in every degree, which
is more than `m`-pseudo-coherence asks of the local approximation.  Nothing about flatness, Tor
amplitude or a derived tensor product enters, so the collapse of the universes which the
Tor-dimension half of that implication is subject to does not apply here.

**No `@[stacks 08G8]` attribute is claimed.**  Stacks 08G8 is an equivalence; this is one clause
of one of its two implications, so the tag would sit on a strictly weaker statement.  The source
file makes the same ruling for the same reason.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]

/-- **A perfect complex of `O`-modules is `m`-pseudo-coherent**, for every integer `m`, at
independent universes.  The strictly perfect local models of a perfect complex map to it by
quasi-isomorphisms, which are isomorphisms on cohomology in all degrees.

This is `AlgebraicGeometry.RingedSite.isPseudoCoherentComplex_of_isPerfectComplex` with the
universe of the sections of the structure sheaf free rather than `0`. -/
theorem isPseudoCoherentComplexFrom_of_isPerfectComplex_general
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : X.IsPerfectComplex E) (m : ℤ) :
    X.IsPseudoCoherentComplexFrom E m := by
  intro U
  obtain ⟨S, hS, hmodels⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels f hf
  let := hq
  exact ⟨P, hP, q, fun _ _ => inferInstance, inferInstance⟩

variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A perfect object of `D(O)` is `m`-pseudo-coherent**, for every integer `m`, at independent
universes.

This is `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect` with the universe of the
sections of the structure sheaf free rather than `0`, and with the integer a parameter rather
than universally quantified inside the conclusion. -/
theorem isPseudoCoherentFrom_of_isPerfect_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E) (m : ℤ) :
    X.IsPseudoCoherentFrom E m := by
  obtain ⟨K, hK, e⟩ := hE
  exact ⟨K, isPseudoCoherentComplexFrom_of_isPerfectComplex_general X hK m, e⟩

end AlgebraicGeometry.RingedSite

end
