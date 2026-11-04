module

public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.TensorExact
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist

/-!
# The twist on projective space over a ring as a functor

`AlgebraicGeometry.projectiveTwist n ℱ d` is the twist of an `𝒪`-module on `ℙⁿ_R` by the
pullback of the `d`-th twisting sheaf of integral projective space. This file promotes it to a
functor `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor n d` whose object map is
`projectiveTwist n · d` on the nose, and proves for it the exactness properties that
`Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor` has on `Proj 𝒜`.

Here `ℙⁿ_R` is a pullback of integral projective space
(`AlgebraicGeometry.projectiveSpaceOverRing`), not a `Proj` term, and its twisting sheaf is a
pullback along `AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse`, not a
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`. Mathematically the twist on `ℙⁿ_R` is
the special case of the `Proj` twist at the polynomial ring, but deriving one from the other
needs the base-change identification of the two spaces, which is not available; so both functors
are built from the shared tensor-functor results instead.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistingSheaf`: the pullback to `ℙⁿ_R` of
  the `d`-th twisting sheaf of integral projective space.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor`: the `d`-th twist as an
  endofunctor of `𝒪_{ℙⁿ_R}`-modules.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistFunctor.projectiveTwistFunctor_obj`: the object map is
  `AlgebraicGeometry.projectiveTwist`, by `rfl`.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.additive_projectiveTwistFunctor`,
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.preservesZeroMorphisms_projectiveTwistFunctor`,
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.preservesFiniteColimits_projectiveTwistFunctor` and
  `Stacks.AlgebraicGeometry.ProjTwistFunctor.exact_map_and_epi_of_shortExact_projective`: the
  twist is additive, preserves zero morphisms and is right exact, with no hypothesis.
* `shortExact_map_projectiveTwistFunctor_of_preservesMonomorphisms` and
  `shortExact_map_projectiveTwistFunctor`, in `Stacks.AlgebraicGeometry.ProjTwistFunctor`: the
  twist of a short exact sequence is short exact when the twist preserves monomorphisms, and when
  it is an equivalence.
* `Stacks.AlgebraicGeometry.ProjTwistFunctor.isEquivalence_projectiveTwistFunctor`: the twist by
  an invertible twisting sheaf is an equivalence.

## Implementation notes

The twisting sheaf is given its own name rather than being written inline as in
`AlgebraicGeometry.projectiveTwist`, because every statement here mentions it and
`AlgebraicGeometry.Scheme.Modules.pullback` is a `Classical.choice`-produced left adjoint, into
which the unifier would otherwise unfold. With the name, the object identification with
`projectiveTwist` is `rfl` without any unfolding of the pullback.

The grading of the polynomial ring is supplied by a local `letI`, as in
`AlgebraicGeometry.projectiveTwist` itself; `MvPolynomial.gradedAlgebra` is not a global
instance.

Invertibility of the pulled-back twisting sheaf is a hypothesis here, although it holds with no
hypothesis on `R`, `n` or `d`: that is
`Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_projectiveTwistingSheaf`, in a module which
imports this one. A consumer should use the unconditional statements there instead of
discharging the hypothesis itself.

No tag attribute is attached: Tag 01YS is the eventual-vanishing statement, of which this is an
input.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {R : Type u} [CommRing R]

/-- The pullback to `ℙⁿ_R` of the `d`-th twisting sheaf of integral projective space, the sheaf
`𝒪_{ℙⁿ_R}(d)` of `AlgebraicGeometry.projectiveTwist`. -/
noncomputable def projectiveTwistingSheaf (n : ℕ) (d : ℤ) :
    SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf := by
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact (Scheme.Modules.pullback
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R)))).obj
    (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)

/-- **The `d`-th twist on `ℙⁿ_R` as a functor.** On objects it is
`AlgebraicGeometry.projectiveTwist n · d`, by `rfl`. -/
noncomputable def projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf ⥤
      SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(projectiveSpaceOverRing n (.of R)).presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (projectiveSpaceOverRing n (.of R)).presheaf
        (forget₂ CommRingCat RingCat) (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2⟩).flip.obj
    (projectiveTwistingSheaf n d)

/-- The twist functor does on objects exactly what the twist does. -/
theorem projectiveTwistFunctor_obj (n : ℕ) (d : ℤ)
    (F : (projectiveSpaceOverRing n (.of R)).Modules) :
    (projectiveTwistFunctor n d).obj F = projectiveTwist n F d := rfl

/-- The twist on `ℙⁿ_R` is an additive functor. -/
instance additive_projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    (projectiveTwistFunctor (R := R) n d).Additive :=
  Stacks.ProjTwistFunctor.additive_tensorRightFunctor
    (projectiveSpaceOverRing n (.of R)).presheaf
    (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
    (projectiveTwistingSheaf n d)

/-- The twist on `ℙⁿ_R` preserves zero morphisms. -/
instance preservesZeroMorphisms_projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    (projectiveTwistFunctor (R := R) n d).PreservesZeroMorphisms :=
  inferInstance

/-- **The twist on `ℙⁿ_R` is right exact.** No hypothesis on `n` or `d`. -/
theorem preservesFiniteColimits_projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    PreservesFiniteColimits (projectiveTwistFunctor (R := R) n d) :=
  Stacks.ProjTwistFunctor.preservesFiniteColimits_tensorRightFunctor
    (projectiveSpaceOverRing n (.of R)).sheaf
    (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
    (projectiveTwistingSheaf n d)

/-- The twist on `ℙⁿ_R` of a short exact sequence is exact with epimorphic second map, with no
hypothesis on `n` or `d`. -/
theorem exact_map_and_epi_of_shortExact_projective (n : ℕ) (d : ℤ)
    {T : ShortComplex
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)}
    (hT : T.ShortExact) :
    (T.map (projectiveTwistFunctor n d)).Exact ∧
      Epi ((projectiveTwistFunctor n d).map T.g) :=
  Stacks.ProjTwistFunctor.exact_map_and_epi_of_shortExact
    (projectiveSpaceOverRing n (.of R)).sheaf
    (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
    (projectiveTwistingSheaf n d) hT

/-- **The twist on `ℙⁿ_R` by a flat twisting sheaf is exact.** -/
theorem shortExact_map_projectiveTwistFunctor_of_preservesMonomorphisms (n : ℕ) (d : ℤ)
    [h : (projectiveTwistFunctor (R := R) n d).PreservesMonomorphisms]
    {T : ShortComplex
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)}
    (hT : T.ShortExact) :
    (T.map (projectiveTwistFunctor n d)).ShortExact := by
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOverRing n (.of R)).sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (projectiveSpaceOverRing n (.of R)).sheaf.obj
          (forget₂ CommRingCat RingCat)
          (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2⟩).flip.obj
      (projectiveTwistingSheaf n d)).PreservesMonomorphisms := h
  exact Stacks.ProjTwistFunctor.shortExact_map_tensorRightFunctor_of_preservesMonomorphisms
    (projectiveSpaceOverRing n (.of R)).sheaf
    (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
    (projectiveTwistingSheaf n d) hT

/-- **The twist on `ℙⁿ_R` by an invertible twisting sheaf is exact**, from the twist being an
equivalence. -/
theorem shortExact_map_projectiveTwistFunctor (n : ℕ) (d : ℤ)
    [(projectiveTwistFunctor (R := R) n d).IsEquivalence]
    {T : ShortComplex
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)}
    (hT : T.ShortExact) :
    (T.map (projectiveTwistFunctor n d)).ShortExact :=
  hT.map_of_exact _

/-- An invertible pulled-back twisting sheaf makes the twist on `ℙⁿ_R` an equivalence. -/
theorem isEquivalence_projectiveTwistFunctor (n : ℕ) (d : ℤ)
    [Stacks.SheafOfModules.IsInvertible (projectiveSpaceOverRing n (.of R)).presheaf
      (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2 (projectiveTwistingSheaf n d)] :
    (projectiveTwistFunctor (R := R) n d).IsEquivalence :=
  Stacks.ProjTwistFunctor.isEquivalence_tensorRightFunctor_of_isInvertible _ _ _

end Stacks.AlgebraicGeometry.ProjTwistFunctor

end
