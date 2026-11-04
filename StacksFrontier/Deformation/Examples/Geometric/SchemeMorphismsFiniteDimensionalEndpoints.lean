module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensionalDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensionalTransport
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExact
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison

/-!
# Finite dimensionality for `Def_{X → Y}` from its endpoints, along the sequence of Tag 0E3V

Let `f : X → Y` be a morphism of schemes over a field `k`. [Stacks Project, Tag 0E3V] gives the
exact sequence of `k`-vector spaces

`0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}`
`  → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`.

This file reads off finite dimensionality of `Inf(Def_{X → Y})` and of `T Def_{X → Y}` from it,
as the source's proof of [Stacks Project, Tag 0E3W] indicates: `Inf(Def_{X → Y})` embeds in
`Inf(Def_X) × Inf(Def_Y)`, and `T Def_{X → Y}` sits between `Der_k(𝒪_Y, f_*𝒪_X)` and
`T Def_X × T Def_Y`.

## Main results

* `Deformation.Examples.finiteDimensional_of_exact`: in an exact sequence `M → N → P` of vector
  spaces with `M` and `P` finite dimensional, `N` is finite dimensional.
* `Deformation.Examples.finiteDimensional_schemeMorphismInf_of_endpoints`: `Inf(Def_{X → Y})`
  at its canonical data is finite dimensional once `Inf(Def_X)` and `Inf(Def_Y)` are.
* `Deformation.Examples.finiteDimensional_schemeMorphismTangent_of_endpoints`:
  `T Def_{X → Y}` is finite dimensional once `T Def_X`, `T Def_Y` and `Der_k(𝒪_Y, f_*𝒪_X)` are.
* `Deformation.Examples.isFiniteDimensionalDeformationCategory_schemeMorphism_of_endpoints`:
  `Def_{X → Y}` satisfies condition (4) of `Deformation.IsFiniteDimensionalDeformationCategory`
  once `Def_X` and `Def_Y` do and `f` and `Y` are proper.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0E3W](https://stacks.math.columbia.edu/tag/0E3W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- **The middle term of an exact sequence of vector spaces with finite dimensional ends is
finite dimensional.** If `M → N → P` is exact with `M` and `P` finite dimensional, then `N` is:
it is an extension of the image of `N` in `P` by the image of `M`. -/
theorem finiteDimensional_of_exact {K M N P : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] {f : M →ₗ[K] N}
    {g : N →ₗ[K] P} (h : Function.Exact f g) [FiniteDimensional K M] [FiniteDimensional K P] :
    FiniteDimensional K N := by
  have h' : Function.Exact f g.rangeRestrict := fun y => by
    rw [← h y, LinearMap.rangeRestrict, Subtype.ext_iff]
    simp
  exact Module.Finite.of_exact h' g.surjective_rangeRestrict

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **`Inf(Def_{X → Y})` is finite dimensional once `Inf(Def_X)` and `Inf(Def_Y)` are**, at the
canonical data of [Stacks Project, Tag 0E3V]: the first arrow of that sequence embeds it in
`Inf(Def_X) × Inf(Def_Y)`. -/
theorem finiteDimensional_schemeMorphismInf_of_endpoints
    (hX :
      letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
        (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
      letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
        (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
      FiniteDimensional k
        (localizedAutomorphismFunctorTangent (schemeMorphismSourcePushforwards f pX pY hf)))
    (hY :
      letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
        (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
      letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
        (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
      FiniteDimensional k
        (localizedAutomorphismFunctorTangent (schemeMorphismTargetPushforwards f pX pY hf))) :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    FiniteDimensional k
      (localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf)) := by
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  have := hX
  have := hY
  exact Module.Finite.of_injective _ (schemeMorphismDeformation_sixTermExact f pX pY hf).1

/-- **`T Def_{X → Y}` is finite dimensional once `T Def_X`, `T Def_Y` and
`Der_k(𝒪_Y, f_*𝒪_X)` are**: by [Stacks Project, Tag 0E3V] it sits in the middle of the exact
sequence `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y} → T Def_X × T Def_Y`. -/
theorem finiteDimensional_schemeMorphismTangent_of_endpoints
    (hX : FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
        (FGModuleCat.of k (ULift.{u} k))))
    (hY : FiniteDimensional k ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
        (FGModuleCat.of k (ULift.{u} k))))
    (hD :
      letI := schemeMorphismDerivationsModule f pY
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
      FiniteDimensional k (schemeMorphismDerivations f pY)) :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
      (FGModuleCat.of k (ULift.{u} k))) := by
  let := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  have := hX
  have := hY
  have := hD
  exact finiteDimensional_of_exact
    (schemeMorphismDeformation_exact_inf_der_tangent f pX pY hf).2.2.2

/-- **Condition (4) for `Def_{X → Y}` from its endpoints.** If `Def_X` and `Def_Y` satisfy
condition (4) of `Deformation.IsFiniteDimensionalDeformationCategory` (finite dimensional
tangent space and infinitesimal automorphisms), `f` is proper and `Y` is proper over `k`, then
`Def_{X → Y}` satisfies it: `Der_k(𝒪_Y, f_*𝒪_X)` is finite dimensional
(`finiteDimensional_schemeMorphismDerivations`), and the sequence of
[Stacks Project, Tag 0E3V] does the rest. -/
theorem isFiniteDimensionalDeformationCategory_schemeMorphism_of_endpoints [IsProper f]
    [IsProper pY]
    (hX : IsFiniteDimensionalDeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsFiniteDimensionalDeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) :
    IsFiniteDimensionalDeformationCategory
      (schemeMorphismDeformationCategoryProjection f pX pY hf) := by
  have hXinf := finiteDimensional_localizedAutomorphismFunctorTangent_of_isFiniteDimensional hX
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    (x := (schemeMorphismSourceForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf))
    (residueFieldBaseIso (Λ := Λ) (k := k)).hom (schemeMorphismSourcePushforwards f pX pY hf)
  have hYinf := finiteDimensional_localizedAutomorphismFunctorTangent_of_isFiniteDimensional hY
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    (x := (schemeMorphismTargetForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf))
    (residueFieldBaseIso (Λ := Λ) (k := k)).hom (schemeMorphismTargetPushforwards f pX pY hf)
  have hXtan := finiteDimensional_tangentModuleAt_of_isFiniteDimensional hX
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
  have hYtan := finiteDimensional_tangentModuleAt_of_isFiniteDimensional hY
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))
  exact isFiniteDimensionalDeformationCategory_of_localized_of_tangentModuleAt
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (x := schemeMorphismTrivialObject f pX pY hf) (residueFieldBaseIso (Λ := Λ) (k := k)).hom
    (schemeMorphismTrivialPushforwards f pX pY hf)
    (finiteDimensional_schemeMorphismInf_of_endpoints f pX pY hf hXinf hYinf)
    (finiteDimensional_schemeMorphismTangent_of_endpoints f pX pY hf hXtan hYtan
      (finiteDimensional_schemeMorphismDerivations f pY))

end Deformation.Examples

end
