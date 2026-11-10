module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensional
public import StacksFrontier.Deformation.Schlessinger.DeformationCategoryHull
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRigidity
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hull and prorepresentability for deformations of a morphism of proper schemes

Let `Λ` be a complete Noetherian local ring with residue field `k` (the classical case) and let
`f : X ⟶ Y` be a morphism of proper schemes over `k`. The functor
`F : 𝒞_Λ → Sets, A ↦ Ob(Def_{X → Y}(A))/≅` of isomorphism classes of deformations of `f`
(Example 0E3T) has a hull, and if `Der_k(𝒪_X, 𝒪_X) = Der_k(𝒪_Y, 𝒪_Y) = 0` then `F` is
prorepresentable. This is Stacks 0ET6.

## Main results

* `Deformation.Examples.exists_hull_schemeMorphismIsomorphismClasses`: **Stacks 0ET6**, the
  hull.
* `Deformation.Examples.isProrepresentableULift_schemeMorphismIsomorphismClasses`:
  **Stacks 0ET6**, prorepresentability.

## Proof

`Def_{X → Y}` is a deformation category by Stacks 0E3U
(`isDeformationCategory_schemeMorphismDeformationCategoryProjection`), and its tangent space is
finite dimensional by Stacks 0E3W
(`isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection`). Hence
the hull exists by Stacks 06J7 and 06IZ, through
`Deformation.exists_hull_isomorphismClasses_of_isDeformationCategory`. If both derivation spaces
vanish, the infinitesimal automorphisms of `Def_{X → Y}` vanish
(`infinitesimalAutomorphisms_schemeMorphismDeformation_eq_bot`, the step the source reads off
Stacks 0E3V and 0DY9), so `F` is a deformation functor equivalent to `Def_{X → Y}`
(Stacks 06K0) and Schlessinger's theorem, Stacks 06JM, applies, through
`Deformation.isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot`.

## Implementation notes

`X` and `Y` are proper `k`-schemes through their structure morphisms `pX` and `pY` to the
spectrum of `k`, and `f` is a morphism over `k` (`hf : f ≫ pY = pX`). The functor `F` is the
canonical functor of fibrewise isomorphism classes `Deformation.isomorphismClasses` of the
deformation category `schemeMorphismDeformationCategoryProjection f pX pY hf`.

`Der_k(𝒪_X, 𝒪_X)` is `Deformation.Examples.schemeMorphismDerivations (𝟙 X) pX`, the
derivations of `𝒪_X` over `k` with values in `𝒪_X`, as in the first display of Stacks 0DY9;
its vanishing is stated as every derivation being zero, as for Stacks 0ET5.

Prorepresentability is stated in the universe-raised form `Deformation.IsProrepresentableULift`,
as for Stacks 0ET1 and 0ET2: the values of `F` lie in the universe of the objects of
`Def_{X → Y}`, not in the morphism universe of `𝒞_Λ`.

## References

* [Stacks Project, Tag 0ET6](https://stacks.math.columbia.edu/tag/0ET6)
* [Stacks Project, Tag 0E3U](https://stacks.math.columbia.edu/tag/0E3U)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0E3W](https://stacks.math.columbia.edu/tag/0E3W)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 06K0](https://stacks.math.columbia.edu/tag/06K0)
* [Stacks Project, Tag 06JM](https://stacks.math.columbia.edu/tag/06JM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The tangent space of `Def_{X → Y}`, in the unlifted model `Deformation.artinianTangentSpace`,
is finite dimensional for a morphism of proper `k`-schemes: Stacks 0E3W, read through the linear
comparison `Deformation.tangentSpaceArtinianLinearEquivUnlifted` of the two tangent-space
models. -/
theorem finiteDimensional_artinianTangentSpace_schemeMorphismIsomorphismClasses
    [IsProper pX] [IsProper pY] :
    letI : Fact (IsPredeformationCategory
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)).p) :=
      ⟨(isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
        hf).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
          hf).predeformation.cofibered))) :=
      ⟨Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory _
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
          hf).predeformation.cofibered)) := by
  let hD := isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf
  obtain ⟨_, hT, -⟩ :=
    isFiniteDimensionalDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf
  let : Fact (IsPredeformationCategory
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)).p) :=
    ⟨hD.predeformation⟩
  have hS := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
    (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)) hD
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      hD.predeformation.cofibered))) := ⟨hS⟩
  have := hT
  exact LinearEquiv.finiteDimensional (tangentSpaceArtinianLinearEquivUnlifted
    (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
    hD.predeformation hS)

/-- **Stacks 0ET6, the hull.** Let `Λ` be a complete local ring with residue field `k` and let
`f : X ⟶ Y` be a morphism of proper `k`-schemes. Then the functor
`A ↦ Ob(Def_{X → Y}(A))/≅` of isomorphism classes of deformations of `f` has a hull: a versal
formal object whose differential is bijective. -/
@[stacks 0ET6 "the functor of isomorphism classes of Def_{X -> Y} has a hull", sga "7 VI 4.9" "(a)"]
theorem exists_hull_schemeMorphismIsomorphismClasses (hΛ : IsClassical Λ k)
    [IsProper pX] [IsProper pY] :
    let G := isomorphismClasses
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
        hf).predeformation.cofibered
    ∃ ξ : FormalObject (Functor.Elements.π G),
      IsHull (categoryOfElements_projection_isCofibered G) ξ :=
  exists_hull_isomorphismClasses_of_isDeformationCategory hΛ
    (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (finiteDimensional_artinianTangentSpace_schemeMorphismIsomorphismClasses f pX pY hf)

/-- **Stacks 0ET6, prorepresentability.** Let `Λ` be a complete local ring with residue field
`k` and let `f : X ⟶ Y` be a morphism of proper `k`-schemes with
`Der_k(𝒪_X, 𝒪_X) = Der_k(𝒪_Y, 𝒪_Y) = 0`. Then the functor `A ↦ Ob(Def_{X → Y}(A))/≅` of
isomorphism classes of deformations of `f` is prorepresentable. -/
@[stacks 0ET6 "if Der_k(O_X, O_X) = Der_k(O_Y, O_Y) = 0, the functor of isomorphism classes of \
Def_{X -> Y} is prorepresentable"]
theorem isProrepresentableULift_schemeMorphismIsomorphismClasses (hΛ : IsClassical Λ k)
    [IsProper pX] [IsProper pY]
    (hX : ∀ D : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X) pX, D = 0)
    (hY : ∀ D : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 Y) pY, D = 0) :
    IsProrepresentableULift (isomorphismClasses
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
        hf).predeformation.cofibered) := by
  let p := schemeMorphismDeformationCategoryProjection (Λ := Λ) (k := k) f pX pY hf
  let hD := isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf
  have hp := hD.predeformation.cofibered
  -- a point over the residue-field object and its pushforward to the dual numbers
  let x : schemeMorphismDeformationCategory f pX pY hf :=
    Over.mk (𝟙 (schemeMorphismFamilySpecialFiber f pX pY hf))
  obtain ⟨y, ι, hι⟩ := exists_pushforward hp (residueFieldBaseIso (Λ := Λ) (k := k)).hom x rfl
  have hy : p.obj y = residueFieldObject.{u, u, u} Λ k :=
    IsHomLift.codomain_eq p (residueFieldBaseIso (Λ := Λ) (k := k)).hom ι
  obtain ⟨z, j, hj⟩ := exists_pushforward hp (dualNumbersInclusion.{u, u, u} (Λ := Λ) (k := k))
    y hy
  have hz : p.obj z = artinianDualNumbers.{u, u, u} Λ k :=
    IsHomLift.codomain_eq p (dualNumbersInclusion.{u, u, u} (Λ := Λ) (k := k)) j
  exact isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot hΛ
    (BasedCategory.ofFunctor p) hD
    (finiteDimensional_artinianTangentSpace_schemeMorphismIsomorphismClasses f pX pY hf)
    (x₀ := ⟨y, hy⟩) (xε := ⟨z, hz⟩) dualNumbersInclusion.{u, u, u}
    (residueMorphism.{u, u, u} (artinianDualNumbers.{u, u, u} Λ k))
    isCanonicalDualNumberPair_dualNumbersInclusion.{u, u, u} j hj
    (infinitesimalAutomorphisms_schemeMorphismDeformation_eq_bot f pX pY hf
      ⟨fun a b => (hX a).trans (hX b).symm⟩ ⟨fun a b => (hY a).trans (hY b).symm⟩ _ _ _ _ _ _)

end Deformation.Examples

end
