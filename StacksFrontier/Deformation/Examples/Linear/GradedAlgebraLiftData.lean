module

public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebras
public import StacksFrontier.RingTheory.BaseChangeAlongSurjection
public import StacksFrontier.RingTheory.GradedAlgebra.LiftPresentation

/-!
# A deformation of a graded algebra, read as a lift of a presentation

A deformation of a graded `k`-algebra `P` over an object `A` of `𝒞_Λ` is, in this repository, a
graded `A`-algebra `Q` finite projective in each degree together with a morphism
`H : Q ⟶ (k, P)` whose underlying module map is recorded as an `IsBaseChange` datum
(`Deformation.Examples.ProjectiveGradedAlgebra.Hom`). The lifting results of
`StacksFrontier/RingTheory/GradedAlgebra/LiftPresentation.lean` ask instead for

* `Q` flat over `A`, and each graded piece of `Q` flat over `A`;
* the reduction `Q → P` **surjective**;
* its kernel exactly `I • Q`, for `I` the kernel of the base morphism `A → k`.

This file performs that translation. Nothing in it is specific to the square-zero extensions
`k[V]`: the base morphism of a morphism of `𝒞_Λ` into the residue-field object is the residue
map, hence surjective, and that is all surjectivity and the kernel computation need.

## Main results

* `Deformation.Examples.hom_residueFieldBase_eq_residue`: a morphism of `𝒞_Λ` into the
  residue-field object is computed by the residue map.
* `Deformation.Examples.surjective_hom_residueFieldBase`: such a morphism is surjective.
* `Deformation.Examples.ProjectiveGradedAlgebra.flat_carrier`: a graded algebra finite
  projective in each degree is flat over its base.
* `Deformation.Examples.ProjectiveGradedAlgebra.surjective_hom_map`: the reduction of a
  deformation is surjective.
* `Deformation.Examples.ProjectiveGradedAlgebra.hom_map_eq_zero_iff`: its kernel is `I • Q`.

## Implementation notes

`hom_residueFieldBase_eq_residue` is strictly more general than the `private`
`base_hom_eq_residue` of
`StacksFrontier/Deformation/Examples/Linear/FiniteProjectiveTangentSpace.lean`, which states the
same thing for morphisms of the category of finite projective modules: the statement is about
`ArtinianLocalAlgCat` alone and mentions no deformation datum.

The three `letI`s before each appeal to `Hom.isBaseChange` are copied verbatim from the field's
own statement; they are the scalar structures along which the base-change datum is phrased, and
the ring map `algebraMap A k` they install is the base morphism itself.

## References

* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u v w m

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A morphism of `𝒞_Λ` into the residue-field object is computed by the residue map.** The
identification of the residue field of `residueFieldBase` with `k` is inverse to its residue
map, so the compatibility condition on residue fields determines the morphism. -/
theorem hom_residueFieldBase_eq_residue {B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : B ⟶ residueFieldBase Λ k) (b : B) :
    f.hom b = B.residueEquiv (IsLocalRing.residue B b) :=
  (residueFieldBase_residueEquiv_residue Λ k (f.hom b)).symm.trans (f.residue_comm b)

/-- A morphism of `𝒞_Λ` into the residue-field object is surjective, being the residue map
followed by an isomorphism. -/
theorem surjective_hom_residueFieldBase {B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : B ⟶ residueFieldBase Λ k) : Function.Surjective f.hom := by
  intro c
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (B.residueEquiv.symm c)
  refine ⟨b, ?_⟩
  rw [hom_residueFieldBase_eq_residue, hb, AlgEquiv.apply_symm_apply]

namespace ProjectiveGradedAlgebra

variable {P : Type m} [CommRing P] [Algebra k P] (grading : ℕ → Submodule k P)
  [GradedAlgebra grading] [∀ d, Module.Finite k (grading d)]

/-- **A graded algebra finite projective in each degree is flat over its base.** Each graded
piece is projective, hence flat, and a module graded by flat submodules is flat by
`Module.Flat.of_decomposition`. -/
theorem flat_carrier (X : ProjectiveGradedAlgebra.{u, w, w, m} Λ k) :
    Module.Flat (↑X.base) X.carrier :=
  let : ∀ i, Module.Flat (↑X.base) (X.grading i) := fun _ => Module.Flat.of_projective
  Module.Flat.of_decomposition X.grading

variable {X : ProjectiveGradedAlgebra.{u, w, w, m} Λ k}
  (H : ProjectiveGradedAlgebra.Hom X (specialFiber (Λ := Λ) P grading))

/-- The reduction of a deformation is surjective with kernel `I • Q`, by base change along the
surjective base morphism. -/
private theorem surjective_and_hom_map_eq_zero_iff :
    Function.Surjective H.map ∧ ∀ y : X.carrier,
      H.map y = 0 ↔ y ∈ RingHom.ker H.base.hom • (⊤ : Submodule (↑X.base) X.carrier) := by
  let : Algebra (↑X.base) (↑(specialFiber (Λ := Λ) P grading).base) := H.base.hom.toAlgebra
  let : Module (↑X.base) (specialFiber (Λ := Λ) P grading).carrier :=
    Module.compHom (specialFiber (Λ := Λ) P grading).carrier H.base.hom.toRingHom
  let : IsScalarTower (↑X.base) (↑(specialFiber (Λ := Λ) P grading).base)
      (specialFiber (Λ := Λ) P grading).carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact ⟨H.isBaseChange.surjective_of_surjective_algebraMap
      (surjective_hom_residueFieldBase H.base),
    H.isBaseChange.eq_zero_iff_mem_ker_smul_top (surjective_hom_residueFieldBase H.base)⟩

/-- **The reduction of a deformation of a graded algebra is surjective.** The base morphism
`A → k` is surjective because `k` is the residue field, and a base change along a surjective
ring map is a surjection. -/
theorem surjective_hom_map : Function.Surjective H.map :=
  (surjective_and_hom_map_eq_zero_iff grading H).1

/-- **The kernel of the reduction of a deformation is `I • Q`**, for `I` the kernel of the base
morphism. This is the hypothesis `hπker` of `Ideal.exists_addMonoidHom_tmul_smul` and of the
lifting results built on it. -/
theorem hom_map_eq_zero_iff (y : X.carrier) :
    H.map y = 0 ↔ y ∈ RingHom.ker H.base.hom • (⊤ : Submodule (↑X.base) X.carrier) :=
  (surjective_and_hom_map_eq_zero_iff grading H).2 y

end ProjectiveGradedAlgebra

end Deformation.Examples

end
