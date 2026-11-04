module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object is pseudo-coherent and locally of finite Tor dimension, at arbitrary universes

This file is the universe-general form of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude`, which
states its results with the sections of the modules (and, where the ring universe enters, of the
structure sheaf) in universe `0`. The statements and proofs below are those of that file at the
universes given in each declaration; each declaration has the name of its counterpart there with
the suffix `_general` (`General` for definitions and instances).

Let `(C, O)` be a ringed site. A perfect complex of `O`-modules is pseudo-coherent, a perfect
object of `D(O)` is pseudo-coherent, and a perfect object of `D(O)` locally has finite Tor
dimension. Together these are the implication (1) ⟹ (2) of Stacks 08G8.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplex_of_isPerfectComplex_general`: a perfect
  complex is pseudo-coherent.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general`: a perfect object of `D(O)`
  is pseudo-coherent.

The Tor-dimension clause on the diagonal `RingedSite.{u, u, u}` is
`Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_isPerfect_anyUniverse`
of `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitude`.

## Implementation notes

Pseudo-coherence is immediate from the definitions: perfectness provides, above a covering of
each object, a strictly perfect complex mapping *quasi-isomorphically* to the restriction, and a
quasi-isomorphism is in particular an isomorphism on cohomology in every degree and an
epimorphism on cohomology in the bottom degree, which is what `m`-pseudo-coherence asks for, for
every `m`.

This file carries **no** `@[stacks 08G8]` attribute: the full statement of Stacks 08G8 is an
equivalence, and only the implication (1) ⟹ (2) is proved here, so the tag would sit on a
strictly weaker statement. The converse implication, which goes through Stacks 08G7
(`Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion_general`), and the
equivalence that the two assemble into — which is where the tag sits — are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectnessCriterion.lean`.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A perfect complex of `O`-modules is `m`-pseudo-coherent for every `m`: the strictly perfect
local models of a perfect complex map to it by quasi-isomorphisms, which are isomorphisms on
cohomology in all degrees. -/
theorem isPseudoCoherentComplex_of_isPerfectComplex_general
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : X.IsPerfectComplex E) :
    X.IsPseudoCoherentComplex E := by
  intro m U
  obtain ⟨S, hS, hmodels⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels f hf
  let := hq
  exact ⟨P, hP, q, fun _ _ => inferInstance, inferInstance⟩

variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- A perfect object of `D(O)` is pseudo-coherent. This is the first clause of the implication
(1) ⟹ (2) of Stacks 08G8. -/
theorem isPseudoCoherent_of_isPerfect_general
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E) :
    X.IsPseudoCoherent E := by
  obtain ⟨K, hK, e⟩ := hE
  exact ⟨K, isPseudoCoherentComplex_of_isPerfectComplex_general X hK, e⟩

end AlgebraicGeometry.RingedSite

end
