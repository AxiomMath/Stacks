module

public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Deformation.Examples.Geometric.SpacesRimSchlessinger
public import StacksFrontier.Deformation.Schlessinger.DeformationCategoryHull
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldComparison
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceFinite

/-!
# Hulls for deformations of a proper algebraic space (Stacks 0ET7)

Let `Λ` be a complete local ring with residue field `k` (the classical case) and let `X` be a
proper algebraic space over `k`, presented on a big fppf site over `Spec Λ` as in Stacks 0E3Z.
The functor `F : A ↦ Ob(Def_X(A))/≅` of isomorphism classes of deformations of `X` has a hull,
and if `Der_k(𝒪_X, 𝒪_X) = 0` it is prorepresentable.

The deformation category `Def_X` is a deformation category by Stacks 0E40, its tangent space is
finite dimensional by Stacks 0E42, and its infinitesimal automorphisms are `Der_k(𝒪_X, 𝒪_X)` by
Stacks 0E41. The general criteria
`Deformation.exists_hull_isomorphismClasses_of_isDeformationCategory` (Stacks 06J7 and 06IZ) and
`Deformation.isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot`
(Stacks 06K0 and 06JM) then give the two assertions.

## Main results

* `Deformation.Examples.exists_hull_spaceIsomorphismClasses`: **Stacks 0ET7**, the hull.
* `Deformation.Examples.isProrepresentableULift_spaceIsomorphismClasses`: **Stacks 0ET7**,
  prorepresentability when `Der_k(𝒪_X, 𝒪_X) = 0`.
* `Deformation.Examples.infinitesimalAutomorphisms_spaceDeformation_eq_bot`: `Inf(Def_X) = 0`
  when `Der_k(𝒪_X, 𝒪_X) = 0`, at every point over `k`, through the group isomorphism
  `Inf(Def_X) ≅ Der_k(𝒪_X, 𝒪_X)` of Stacks 0E41.

## Implementation notes

"`Λ` is a complete local ring with residue field `k`" is `Deformation.IsClassical Λ k`, the
classical case of Stacks 06GC, as in Stacks 0ET4, 0ET5 and 0ET6. Properness of `X` over `k` is
`AlgebraicGeometry.Space.IsProper` (Stacks 03ZM) of the structure morphism `toK`.
`Der_k(𝒪_X, 𝒪_X)` is the type of derivations of the structure sheaf of the small étale site of
`X` along the structure map `toK⁻¹𝒪_{Spec k} ⟶ 𝒪_X`, the type of Stacks 0E41.

Prorepresentability is stated in the universe-raised form `Deformation.IsProrepresentableULift`:
the values of `F` lie in the universe of the objects of `Def_X`, not in the morphism universe of
`𝒞_Λ`.

## References

* [Stacks Project, Tag 0ET7](https://stacks.math.columbia.edu/tag/0ET7)
* [Stacks Project, Tag 0E40](https://stacks.math.columbia.edu/tag/0E40)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0E42](https://stacks.math.columbia.edu/tag/0E42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **`Inf(Def_X) = 0` when `Der_k(𝒪_X, 𝒪_X) = 0`.** For an algebraic space `X` over `k` without
nonzero `k`-derivations of its structure sheaf, the infinitesimal automorphisms of its deformation
category vanish, at every point over `k` and every pushforward of it along a dual-number pair:
they form a group isomorphic to `Der_k(𝒪_X, 𝒪_X)` by Stacks 0E41. -/
public theorem infinitesimalAutomorphisms_spaceDeformation_eq_bot
    (hDer : ∀ D : SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK), D = 0)
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e) (i : x₀.1 ⟶ xε.1)
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    infinitesimalAutomorphisms
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
        toK).predeformation.cofibered g e hpair i hi = ⊥ := by
  have : Subsingleton (Multiplicative
      (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK))) :=
    ⟨fun a b => Multiplicative.toAdd.injective ((hDer _).trans (hDer _).symm)⟩
  have : Subsingleton (infinitesimalAutomorphismGroup
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation
      g e hpair i hi) :=
    (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i
      _ hi).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

/-- **Stacks 0ET7, the hull.** Let `Λ` be a complete local ring with residue field `k` and let
`X` be a proper algebraic space over `k`. Then the functor `A ↦ Ob(Def_X(A))/≅` of isomorphism
classes of deformations of `X` has a hull: a versal formal object whose differential is
bijective. -/
@[stacks 0ET7 "for a proper algebraic space X over k and Λ complete local with residue field k, \
the functor of isomorphism classes of Def_X has a hull"]
public theorem exists_hull_spaceIsomorphismClasses (hcl : IsClassical Λ k)
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK) :
    let G := isomorphismClasses
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
        toK).predeformation.cofibered
    ∃ ξ : FormalObject (CategoryOfElements.π G),
      IsHull (categoryOfElements_projection_isCofibered G) ξ :=
  exists_hull_isomorphismClasses_of_isDeformationCategory hcl
    (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
    (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK)
    (spaceTangentSpace_finiteDimensional B hΛ hSpec X hX toK hproper)

/-- **Stacks 0ET7, prorepresentability.** Let `Λ` be a complete local ring with residue field
`k` and let `X` be a proper algebraic space over `k` with `Der_k(𝒪_X, 𝒪_X) = 0`. Then the functor
`A ↦ Ob(Def_X(A))/≅` of isomorphism classes of deformations of `X` is prorepresentable. -/
@[stacks 0ET7 "if Der_k(O_X, O_X) = 0, the functor of isomorphism classes of Def_X is \
prorepresentable"]
public theorem isProrepresentableULift_spaceIsomorphismClasses (hcl : IsClassical Λ k)
    (hproper : Space.IsProper B (Spec (.of Λ)) hΛ toK)
    (hDer : ∀ D : SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK), D = 0) :
    IsProrepresentableULift (isomorphismClasses
      (BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK))
      (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX
        toK).predeformation.cofibered) := by
  let p := spaceDeformationProjection B hΛ hSpec X hX toK
  let hD := isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK
  have hp := hD.predeformation.cofibered
  -- a point over the residue-field object and its pushforward to the dual numbers
  let x : Over (spaceSpecialFiber B hΛ hSpec X hX toK) :=
    Over.mk (𝟙 (spaceSpecialFiber B hΛ hSpec X hX toK))
  obtain ⟨y, ι, hι⟩ := exists_pushforward hp (residueFieldBaseIso (Λ := Λ) (k := k)).hom x rfl
  have hy : p.obj y = residueFieldObject.{u, u, u} Λ k :=
    IsHomLift.codomain_eq p (residueFieldBaseIso (Λ := Λ) (k := k)).hom ι
  obtain ⟨z, j, hj⟩ := exists_pushforward hp (dualNumbersInclusion.{u, u, u} (Λ := Λ) (k := k))
    y hy
  have hz : p.obj z = artinianDualNumbers.{u, u, u} Λ k :=
    IsHomLift.codomain_eq p (dualNumbersInclusion.{u, u, u} (Λ := Λ) (k := k)) j
  exact isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot hcl
    (BasedCategory.ofFunctor p) hD (spaceTangentSpace_finiteDimensional B hΛ hSpec X hX toK hproper)
    (x₀ := ⟨y, hy⟩) (xε := ⟨z, hz⟩) dualNumbersInclusion.{u, u, u}
    (residueMorphism.{u, u, u} (artinianDualNumbers.{u, u, u} Λ k))
    isCanonicalDualNumberPair_dualNumbersInclusion.{u, u, u} j hj
    (infinitesimalAutomorphisms_spaceDeformation_eq_bot B hΛ hSpec X hX toK hDer _ _ _ _ _)

end Deformation.Examples

end
