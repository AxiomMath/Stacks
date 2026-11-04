module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyBoundedHomComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation
import StacksCore.Tactic.StacksAttribute

/-!
# The derived dual of a locally bounded strictly perfect complex on a ringed space

Let `(X, 𝒪_X)` be a ringed space and let `𝓔^•` be a complex of `𝒪_X`-modules which is strictly
perfect on the members of an open covering of `X` — bounded there, with each of its terms there a
direct summand of a finite free module — but not necessarily on `X` itself. Then

`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_X))`:

the derived dual of the object of `D(𝒪_X)` represented by `𝓔^•` is represented by the ordinary
internal Hom complex of `𝓔^•` into the structure sheaf.

This is the local form of [Stacks, Tag 08DM] on a ringed space. The global form,
`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso`, asks `𝓔^•` to be bounded on `X` with
every term a direct summand of a finite free `𝒪_X`-module, and neither holds for the complexes
the Chow chapter produces: a perfect object of `D(𝒪_X)` whose Chern classes are defined is
represented, after pulling back along an envelope, by a complex of finite locally free modules
which is only locally bounded ([Stacks, Tag 0GUJ]).

## Main results

* `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_coversTop`: the comparison
  `Q(SheafHom(𝓔^•, 𝓕^•)) ⟶ RSheafHom(𝓔^•, 𝓕^•)` is an isomorphism for every target, for a source
  that is strictly perfect only on the members of an open covering.
* `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_locally`: the same with the
  covering presented pointwise, as a neighbourhood of each point.
* `Stacks.SheafOfModules.derivedDualQIso`: **`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_X))`.**

## Implementation notes

The whole content is in the site-level
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_coversTop`; the site of a
ringed space is `Stacks.SheafOfModules.ringedSite`, whose objects are the opens of `X` and whose
topology is the open-cover topology, so the covering hypothesis is literally a family of opens
covering `X` and `TopologicalSpace.Opens.coversTop_iff` is the passage between the two phrasings.

`Stacks.SheafOfModules.derivedDualQIso` is the inverse of the comparison at the target
`AlgebraicGeometry.RingedSite.structureSheafComplex`, whose class is
`AlgebraicGeometry.RingedSite.derivedStructureSheaf` — so the target of the comparison there is
`Stacks.SheafOfModules.derivedDual Rc (Q 𝓔^•)` on the nose, by
`Stacks.SheafOfModules.derivedDual_eq`.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

universe u

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- **[Stacks, Tag 08DM] for a source that is strictly perfect only locally.** Let `U : ι → `
`Opens X` be a family of opens covering `X` and let `𝓔^•` be a complex of `𝒪_X`-modules whose
restriction to each `U i` has finitely many nonzero terms, each of them a direct summand of a
finite free `𝒪_{U i}`-module. Then, for every complex `𝓕^•`, the canonical comparison from the
class of the internal Hom complex `SheafHom(𝓔^•, 𝓕^•)` to the derived internal Hom
`RSheafHom(𝓔^•, 𝓕^•)` is an isomorphism.

Neither the global bound of `strictlyPerfectHomComparison_isIso` nor the global splittings of
its termwise hypothesis are needed; this is the ringed-space reading of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_coversTop`. -/
theorem strictlyPerfectHomComparison_isIso_of_coversTop
    (E F : CochainComplex (StructureSheafModules Rc) ℤ)
    {ι : Type*} {U : ι → Opens X} (hU : (Opens.grothendieckTopology X).CoversTop U)
    (hbdd : ∀ i, {n : ℤ |
      ¬ IsZero ((RingedSite.restrictComplex (ringedSite Rc) E (U i)).X n)}.Finite)
    (hterm : ∀ (i : ι) (n : ℤ), RingedSite.IsFiniteFreeSummand ((ringedSite Rc).over (U i))
      ((RingedSite.restrictComplex (ringedSite Rc) E (U i)).X n)) :
    IsIso (strictlyPerfectHomComparison Rc E F) :=
  RingedSite.strictlyPerfectHomComparison_isIso_of_coversTop (ringedSite Rc)
    (derivedInternalHom Rc) E F hU hbdd hterm

/-- **[Stacks, Tag 08DM] for a source that is strictly perfect only locally**, with the covering
presented pointwise: it is enough that every point of `X` have an open neighbourhood on which
`𝓔^•` has finitely many nonzero terms, each of them a direct summand of a finite free module.

`TopologicalSpace.Opens.coversTop_iff` turns the pointwise phrasing into the covering family
`strictlyPerfectHomComparison_isIso_of_coversTop` consumes. -/
theorem strictlyPerfectHomComparison_isIso_of_locally
    (E F : CochainComplex (StructureSheafModules Rc) ℤ)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      {n : ℤ | ¬ IsZero ((RingedSite.restrictComplex (ringedSite Rc) E U).X n)}.Finite ∧
      ∀ n : ℤ, RingedSite.IsFiniteFreeSummand ((ringedSite Rc).over U)
        ((RingedSite.restrictComplex (ringedSite Rc) E U).X n)) :
    IsIso (strictlyPerfectHomComparison Rc E F) :=
  strictlyPerfectHomComparison_isIso_of_coversTop Rc E F
    (U := fun x : X => (h x).choose)
    ((Opens.coversTop_iff _ _).mpr (IsOpenCover.mk (top_le_iff.mp fun x _ =>
      Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩)))
    (fun x => (h x).choose_spec.2.1) (fun x => (h x).choose_spec.2.2)

/-- **The derived dual of a locally strictly perfect complex is its naive dual complex**:
`(Q 𝓔^•)^∨ ≅ Q(SheafHom^•(𝓔^•, 𝒪_X))`, for a complex `𝓔^•` of `𝒪_X`-modules which is bounded
with split terms on the members of an open covering of `X`.

This is `strictlyPerfectHomComparison_isIso_of_locally` at the target
`AlgebraicGeometry.RingedSite.structureSheafComplex`, read through
`Stacks.SheafOfModules.derivedDual_eq`. -/
def derivedDualQIso (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      {n : ℤ | ¬ IsZero ((RingedSite.restrictComplex (ringedSite Rc) E U).X n)}.Finite ∧
      ∀ n : ℤ, RingedSite.IsFiniteFreeSummand ((ringedSite Rc).over U)
        ((RingedSite.restrictComplex (ringedSite Rc) E U).X n)) :
    derivedDual Rc (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) E
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj :=
  letI := strictlyPerfectHomComparison_isIso_of_locally Rc E
    (RingedSite.structureSheafComplex (ringedSite Rc)) h
  (asIso (strictlyPerfectHomComparison Rc E
    (RingedSite.structureSheafComplex (ringedSite Rc)))).symm

end Stacks.SheafOfModules

end
