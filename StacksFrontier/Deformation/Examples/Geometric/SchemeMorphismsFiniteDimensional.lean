module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensionalEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemesFiniteDimensional

/-!
# Finite dimensionality of `Inf` and `T` of deformations of a morphism of proper schemes

Let `f : X → Y` be a morphism of schemes over a field `k`, in the setting of Example 0DY7, and let
`Def_{X → Y}` be its deformation category (Example 0E3T, a deformation category by Lemma 0E3U).
[Stacks Project, Tag 0E3W] states that if `X` and `Y` are both proper over `k`, then
`Inf(Def_{X → Y})` and `T Def_{X → Y}` are finite dimensional.

The source omits the proof, with the hint: argue as in [Stacks Project, Tag 0DYA] and use the
exact sequence of [Stacks Project, Tag 0E3V],

`0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}`
`  → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`.

The proof given here:

* `Inf(Def_X)`, `Inf(Def_Y)`, `T Def_X` and `T Def_Y` are finite dimensional by
  [Stacks Project, Tag 0DYA], `X` and `Y` being proper over `k`;
* `Der_k(𝒪_Y, f_*𝒪_X) = Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)` is finite dimensional, arguing as in
  Tag 0DYA: `f` is proper (`X` is proper and `Y` separated over `k`), so `f_*𝒪_X` is coherent
  ([Stacks Project, Tag 02O5]), `Ω_{Y/k}` is coherent, and `Ext⁰` between coherent modules on
  the proper `k`-scheme `Y` is finite dimensional ([Stacks Project, Tag 0D0D])
  (`Deformation.Examples.finiteDimensional_schemeMorphismDerivations`);
* `Inf(Def_{X → Y})` embeds in `Inf(Def_X) × Inf(Def_Y)` by exactness at the first spot, and
  `T Def_{X → Y}` is the middle term of the exact
  `Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y} → T Def_X × T Def_Y`, so both are finite dimensional
  (`Deformation.Examples.isFiniteDimensionalDeformationCategory_schemeMorphism_of_endpoints`).

The conclusion is stated as condition (4) of `Deformation.IsFiniteDimensionalDeformationCategory`
(a deformation category whose tangent space and whose infinitesimal automorphisms, at every point
over `k` and every choice of pushforwards, are finite dimensional); the two terms of the sequence
of Tag 0E3V at its canonical data are finite dimensional as well.

## Main results

* `isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection`:
  [Stacks Project, Tag 0E3W].
* `Deformation.Examples.finiteDimensional_schemeMorphismInf`,
  `Deformation.Examples.finiteDimensional_schemeMorphismTangent`: the terms `Inf(Def_{X → Y})`
  and `T Def_{X → Y}` of the sequence of Tag 0E3V.

## References

* [Stacks Project, Tag 0E3W](https://stacks.math.columbia.edu/tag/0E3W)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0DYA](https://stacks.math.columbia.edu/tag/0DYA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

include hf in
/-- A morphism of schemes proper over `k` is proper: `f ≫ pY = pX` is proper and `pY` is
separated. -/
theorem isProper_of_isProper_structureMorphisms [IsProper pX] [IsProper pY] : IsProper f := by
  have : IsProper (f ≫ pY) := hf ▸ ‹IsProper pX›
  exact IsProper.of_comp f pY

/-- **Stacks Project, Tag 0E3W.** In the setting of Tag 0E3V — a morphism `f : X → Y` of schemes
over the field `k` — if `X` and `Y` are both proper over `k`, then `Inf(Def_{X → Y})` and
`T Def_{X → Y}` are finite dimensional.

The statement is condition (4) of `Deformation.IsFiniteDimensionalDeformationCategory` for the
deformation category `Def_{X → Y}` of Example 0E3T: it is a deformation category, its tangent
space `T Def_{X → Y}` (isomorphism classes over the dual numbers, with the vector space structure
of Tag 06IH) is finite dimensional, and its infinitesimal automorphisms are finite dimensional at
every point over `k` and every choice of pushforwards. -/
@[stacks 0E3W "for a morphism f : X -> Y of schemes over k with X and Y both proper over k, \
Inf(Def_{X -> Y}) and T Def_{X -> Y} are finite dimensional; stated as condition (4) of \
Deformation.IsFiniteDimensionalDeformationCategory: the tangent space, and the infinitesimal \
automorphisms at every point over k and every choice of pushforwards, are finite dimensional"]
theorem isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection
    [IsProper pX] [IsProper pY] :
    IsFiniteDimensionalDeformationCategory
      (schemeMorphismDeformationCategoryProjection f pX pY hf) := by
  have := isProper_of_isProper_structureMorphisms f pX pY hf
  have : IsProper (Over.mk pX : Over (Spec (CommRingCat.of k))).hom := ‹IsProper pX›
  have : IsProper (Over.mk pY : Over (Spec (CommRingCat.of k))).hom := ‹IsProper pY›
  exact isFiniteDimensionalDeformationCategory_schemeMorphism_of_endpoints f pX pY hf
    (isFiniteDimensionalDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ)
      (Over.mk pX))
    (isFiniteDimensionalDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ)
      (Over.mk pY))

/-- **Tag 0E3W, the `Inf` term of the sequence of Tag 0E3V.** For `X` and `Y` proper over `k`,
the infinitesimal automorphisms of `Def_{X → Y}` at its canonical data
(`schemeMorphismTrivialPushforwards`) form a finite dimensional `k`-vector space. -/
theorem finiteDimensional_schemeMorphismInf [IsProper pX] [IsProper pY] :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    FiniteDimensional k
      (localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf)) :=
  finiteDimensional_localizedAutomorphismFunctorTangent_of_isFiniteDimensional
    (isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    (x := schemeMorphismTrivialObject f pX pY hf) (residueFieldBaseIso (Λ := Λ) (k := k)).hom
    (schemeMorphismTrivialPushforwards f pX pY hf)

/-- **Tag 0E3W, the `T` term of the sequence of Tag 0E3V.** For `X` and `Y` proper over `k`, the
tangent module of `Def_{X → Y}` over the dual numbers `k[ε]` is a finite dimensional `k`-vector
space. -/
theorem finiteDimensional_schemeMorphismTangent [IsProper pX] [IsProper pY] :
    FiniteDimensional k ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
      (FGModuleCat.of k (ULift.{u} k))) :=
  finiteDimensional_tangentModuleAt_of_isFiniteDimensional
    (isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)

end Deformation.Examples

end
