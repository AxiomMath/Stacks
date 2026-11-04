module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleQuotientSections
public import StacksFrontier.RingTheory.Fitting.LocalFiltration

/-!
# The graded piece of a pair of comparable subsheaves, and its sections

A filtration of a sheaf of modules by subsheaves has graded pieces `𝒩'/𝒩`, one for each step
`𝒩 ≤ 𝒩'`. This file defines that quotient and computes its sections over an affine open: they are
the quotient of the sections, `Γ(𝒩', V) / Γ(𝒩, V)`.

`AlgebraicGeometry.sectionsSubmoduleQuotientEquivOfAffineOpen` already does this for the quotient
of the *ambient* sheaf by one subsheaf, `Γ(ℱ/𝒩, V) = Γ(ℱ, V)/𝒩(V)`. The quotient of one subsheaf
by a smaller one is not an instance of that, because the ambient sheaf of the inclusion is `𝒩'`
rather than `ℱ`, and the relevant ring-level object is
`Stacks.FittingFiltration.gradedQuot`, the quotient of one submodule by the part of another lying
inside it.

## Main definitions

* `AlgebraicGeometry.submoduleGraded`: the graded piece `𝒩'/𝒩` of a step of a filtration by
  subsheaves, as an object of `X.Modules`.
* `AlgebraicGeometry.submoduleGradedSectionsEquiv`: over an affine open its sections are the
  ring-level graded piece `Stacks.FittingFiltration.gradedQuot` of the two submodules of sections.

## Main results

* `AlgebraicGeometry.range_sectionsLinearMap_homOfLEModules`: the sections of the inclusion
  `𝒩 ⟶ 𝒩'` have range the part of `𝒩(V)` lying inside `𝒩'(V)`. True over every open, with no
  affineness and no quasi-coherence.

## Implementation notes

Both statements are the analogues for `AlgebraicGeometry.SheafOfModules.Submodule.homOfLEModules`
of the two for `SheafOfModules.Submodule.ι` in
`StacksFrontier.AlgebraicGeometry.Modules.SubmoduleQuotientSections`, and the proofs are the same:
the inclusion is sectionwise the inclusion of a submodule, and
`AlgebraicGeometry.sectionsCokernelEquivOfAffineOpen` turns that into the quotient over an affine
open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The graded piece `𝒩'/𝒩` of a step of a filtration by subsheaves**, as an object of
`X.Modules`: the cokernel of the inclusion of the smaller subsheaf into the larger. -/
def submoduleGraded {N N' : F.Submodule} (hle : N ≤ N') : X.Modules :=
  cokernel (SheafOfModules.Submodule.homOfLEModules hle)

/-- **The range of the sections of an inclusion of subsheaves is the part of the smaller lying
inside the larger.** True over every open, with no affineness and no quasi-coherence: the
inclusion is sectionwise the inclusion of a submodule. -/
theorem range_sectionsLinearMap_homOfLEModules {N N' : F.Submodule} (hle : N ≤ N')
    (U : X.Opens) :
    LinearMap.range (Scheme.Modules.sectionsLinearMap
        (SheafOfModules.Submodule.homOfLEModules hle) U)
      = Submodule.comap (sectionsSubmodule N' U).subtype (sectionsSubmodule N U) :=
  Submodule.ext fun s => by
    refine ⟨?_, fun hs => ⟨⟨s.1, hs⟩, rfl⟩⟩
    rintro ⟨t, rfl⟩
    exact t.2

/-- **The sections of a subsheaf over an open are the submodule of sections.** The two are
definitionally equal; this is the respelling that lets a statement about the subsheaf's sections
be read as a statement about a submodule of `Γ(ℱ, U)`, which is where the ring-level filtration
theory lives. -/
def sectionsSubmoduleEquiv (N : F.Submodule) (U : X.Opens) :
    Γ(N.asModules, U) ≃ₗ[Γ(X, U)] ↥(sectionsSubmodule N U) where
  toFun s := ⟨s.1, s.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The respelling carries the range of the sections of an inclusion of subsheaves onto the part
of the smaller subsheaf's sections lying inside the larger's. -/
theorem map_range_sectionsSubmoduleEquiv {N N' : F.Submodule} (hle : N ≤ N') (U : X.Opens) :
    Submodule.map (sectionsSubmoduleEquiv N' U : Γ(N'.asModules, U) →ₗ[Γ(X, U)] _)
        (LinearMap.range (Scheme.Modules.sectionsLinearMap
          (SheafOfModules.Submodule.homOfLEModules hle) U))
      = Submodule.comap (sectionsSubmodule N' U).subtype (sectionsSubmodule N U) := by
  rw [range_sectionsLinearMap_homOfLEModules hle U]
  refine Submodule.ext fun s => ⟨?_, fun hs => ⟨s, hs, rfl⟩⟩
  rintro ⟨t, ht, rfl⟩
  exact ht

/-- **Over an affine open the sections of a graded piece are the graded piece of the sections.**
For `V` affine and both subsheaves quasi-coherent, `Γ(𝒩'/𝒩, V)` is the ring-level graded piece
`Stacks.FittingFiltration.gradedQuot (𝒩(V)) (𝒩'(V))`, which for `𝒩 ≤ 𝒩'` is `𝒩'(V)/𝒩(V)`. -/
def submoduleGradedSectionsEquiv {N N' : F.Submodule} (hle : N ≤ N')
    [N.asModules.IsQuasicoherent] [N'.asModules.IsQuasicoherent] (V : X.affineOpens) :
    Stacks.FittingFiltration.gradedQuot (sectionsSubmodule N V.1) (sectionsSubmodule N' V.1)
      ≃ₗ[Γ(X, V.1)] Γ(submoduleGraded hle, V.1) :=
  (Submodule.Quotient.equiv _ _ (sectionsSubmoduleEquiv N' V.1).symm
      (by rw [← map_range_sectionsSubmoduleEquiv hle V.1, Submodule.map_symm_eq_iff])).trans
    (sectionsCokernelEquivOfAffineOpen (SheafOfModules.Submodule.homOfLEModules hle) V)

end AlgebraicGeometry

end
