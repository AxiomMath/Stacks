module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# A perfect object is pseudo-coherent, at independent universes

Let `(C, O)` be a ringed site.  A perfect complex of `O`-modules is pseudo-coherent, and so is a
perfect object of `D(O)`: perfectness provides, over a covering of each object, a strictly
perfect complex mapping quasi-isomorphically to the restriction, and a quasi-isomorphism is an
isomorphism on cohomology in every degree, which is more than `m`-pseudo-coherence asks for.

This is the first clause of the implication (1) ⟹ (2) of Stacks 08G8.  The library states it
at `RingedSite.{u, v, 0}`
(`AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect`), which does not reach the small
étale ringed site of an algebraic space over `Scheme.{u}`, a `RingedSite.{u + 1, u, u}`; the
proof here is the same, at independent universes.  For a perfect object of `D(O)` with the
modules at the universe of the structure sheaf, the statement is
`AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect_general` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral`.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplex_of_isPerfectComplex_anyModuleUniverse`
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_anyModuleUniverse`

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

omit [∀ (U : X.C), (X.J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- A perfect complex of `O`-modules is `m`-pseudo-coherent for every `m`, at independent
universes. -/
theorem isPseudoCoherentComplex_of_isPerfectComplex_anyModuleUniverse
    {E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : X.IsPerfectComplex E) :
    X.IsPseudoCoherentComplex E := by
  intro n U
  obtain ⟨S, hS, hmodels⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels f hf
  exact ⟨P, hP, q, fun _ _ => inferInstance, inferInstance⟩

variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [∀ (U : X.C), (X.J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- A perfect object of `D(O)` is `n`-pseudo-coherent for every `n`, at independent
universes, the sections of the modules in a universe `m` of their own.
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isPerfect_general` is the case where the
modules and the structure sheaf share a universe. -/
theorem isPseudoCoherentFrom_of_isPerfect_anyModuleUniverse
    {E : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E) (n : ℤ) :
    X.IsPseudoCoherentFrom E n := by
  obtain ⟨K, hK, e⟩ := hE
  exact ⟨K, isPseudoCoherentComplex_of_isPerfectComplex_anyModuleUniverse X hK n, e⟩

end AlgebraicGeometry.RingedSite

end
