module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.BraidingIsoEqCanonicalProof

/-!
# The commutativity constraint of [Stacks, Tag 0FPT] is involutive

`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` is the commutativity
constraint of [Stacks, Tag 0FPT] in the spelling in which the square of [Stacks, Tag 0G77] is
written: the isomorphism `A ⊗^𝐋 B ≅ B ⊗^𝐋 A` obtained by descending the Koszul symmetry of
complexes through the K-flat comparisons of [Stacks, Tag 06YU].
`Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical` identifies `braidingIso` with
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of the symmetric
monoidal structure `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, and a
symmetric monoidal category has `β_ A B ≫ β_ B A = 𝟙`.  Transporting that along the
identification gives involutivity for `braidingIso` at arbitrary objects of `D(𝒪_W)`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.canonicalBraidingHom_symmetry`: the braiding of the
  re-seated structure is involutive, which is `CategoryTheory.SymmetricCategory.symmetry` read
  at the re-seated structure of a ringed space.
* `Stacks.Cohomology.SupportedComplexes.braidingIso_hom_comp_braidingIso_hom`: the two
  composites of the constraint of Tag 0FPT at `(A, B)` and at `(B, A)` are the identity.
* `Stacks.Cohomology.SupportedComplexes.braidingIso_inv_eq_braidingIso_hom`: **the involutivity
  itself**, `(braidingIso A B).inv = (braidingIso B A).hom`, for arbitrary objects of `D(𝒪_W)`
  and every ringed space `W`.

## Implementation notes

The instance binders `HasSheafify` and `WEqualsLocallyBijective` on the site of opens are
discharged unconditionally for every ringed space, by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`; they are switched on as local
instances here, so the statements below are unconditional in `W`.

No `@[stacks]` attribute is attached.  Involutivity of the commutativity constraint is a clause
of [Stacks, Tag 0FPT], which the chapter attributes on the module that constructs the
constraint, and the statements below are inputs to the proof of [Stacks, Tag 0G77] rather than
clauses of its statement.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

attribute [local instance] Stacks.Cohomology.DerivedPullbackTensor.abelianModulesSheafTensor
  Stacks.Cohomology.DerivedPullbackTensor.monoidalModules
  Stacks.Cohomology.DerivedPullbackTensor.symmetricModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalPreadditiveModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalClosedModules
  Stacks.Cohomology.DerivedPullbackTensor.hasTensorModules
  Stacks.Cohomology.DerivedPullbackTensor.monoidalComplexes
  CochainComplex.symmetricCategory

attribute [local implicit_reducible] structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

/-- Two morphisms known to compose to an identity, each given by an equation: the identity
transports.  Stated with every object and morphism a variable, so that it is applied by `exact`
at `default` transparency — the spellings of the derived tensor product below are not
type-correct at the `implicit` transparency at which `rw` re-checks its goal. -/
private theorem comp_eq_id_of_eq {E : Type*} [Category E] {x y : E} {p p' : x ⟶ y}
    {q q' : y ⟶ x} (hp : p = p') (hq : q = q') (h : p ≫ q = CategoryStruct.id x) :
    p' ≫ q' = CategoryStruct.id x := hp ▸ hq ▸ h

/-- An isomorphism whose `hom` composes with `q` to the identity has `q` for its inverse.
An all-variables lemma, for the same reason as `comp_eq_id_of_eq`. -/
private theorem iso_inv_eq_of_hom_comp_eq_id {E : Type*} [Category E] {x y : E} (e : x ≅ y)
    (q : y ⟶ x) (h : e.hom ≫ q = CategoryStruct.id x) : e.inv = q := by
  have h1 : e.inv ≫ e.hom ≫ q = q := Iso.inv_hom_id_assoc e q
  rw [h, Category.comp_id] at h1
  exact h1

variable (W : RingedSpace.{u, u})

/-- **The braiding of the re-seated symmetric monoidal derived category is involutive.**  This is
`CategoryTheory.SymmetricCategory.symmetry` for
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, read at the pinned spelling
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` of its braiding, which is that
braiding by `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom_eq`. -/
theorem canonicalBraidingHom_symmetry
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    canonicalBraidingHom W.sheaf A B ≫ canonicalBraidingHom W.sheaf B A =
      CategoryStruct.id _ :=
  @CategoryTheory.SymmetricCategory.symmetry
    (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules W.sheaf) _
    (canonicalDerivedMonoidal W.sheaf) (canonicalDerivedSymmetric W.sheaf) A B

/-- **The commutativity constraint of [Stacks, Tag 0FPT] composed with itself is the identity**,
at the `braidingIso` spelling: `braidingIso` is `canonicalBraidingHom` by
`Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical`, and that is involutive. -/
theorem braidingIso_hom_comp_braidingIso_hom
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    ((canonicalDerivedTensorProduct W.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite W) A B).hom ≫
        ((canonicalDerivedTensorProduct W.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite W) B A).hom =
      CategoryStruct.id _ :=
  comp_eq_id_of_eq (braidingIsoEqCanonical W A B) (braidingIsoEqCanonical W B A)
    (canonicalBraidingHom_symmetry W A B)

/-- **The commutativity constraint of [Stacks, Tag 0FPT] is involutive**: the inverse of the
constraint at `(A, B)` is the constraint at `(B, A)`, for arbitrary objects of `D(𝒪_W)`.  It
follows from `Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical` and the symmetry axiom of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`. -/
theorem braidingIso_inv_eq_braidingIso_hom
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    ((canonicalDerivedTensorProduct W.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite W) A B).inv =
      ((canonicalDerivedTensorProduct W.sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite W) B A).hom :=
  iso_inv_eq_of_hom_comp_eq_id _ _ (braidingIso_hom_comp_braidingIso_hom W A B)

end Stacks.Cohomology.SupportedComplexes

end
