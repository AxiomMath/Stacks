module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearExtZero
public import StacksFrontier.Deformation.Examples.Geometric.SpacesFiniteDimensionalResidueFieldAction

/-!
# Stacks 0E41, first display: the infinitesimal automorphisms of an algebraic space

Let `k` be a field and `X` an algebraic space over `k`, with deformation category `𝓓_X` of
Example [Stacks Project, Tag 0E3Z].  The first display of [Stacks Project, Tag 0E41] is

`Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`.

This file states it as three identifications, at every choice of the data `Inf(𝓓_X)` is formed
from in [Stacks Project, Tag 06JS]: a point `x₀` of `𝓓_X` over `k`, a pushforward `x₀ ⟶ xε` of
it to an object of `𝒞_Λ` with a dual-number coordinate (the trivial deformation
`X ×_{Spec k} Spec k[ε]` is one), and the dual-number pair `k → k[ε] → k`.

* `Inf(𝓓_X) ≅ Der_k(𝒪_X, 𝒪_X)` as **groups**: `Inf(𝓓_X)` is the group of automorphisms of the
  total space `X'` of `xε` over `Spec k[ε]` which are the identity on `X`, and composition of
  such automorphisms is addition of derivations
  (`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations`).
* `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) ≅ Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` additively: `NL_{X/k}` lives in degrees
  `-1, 0` and its `H⁰` is `Ω_{X/k}` (Stacks 0D0Y), read through the universal property of
  `Ω_{X/k}` (`AlgebraicGeometry.Space.naiveCotangentExtZeroAddEquivDifferentialsHom`).
* `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) ≅ Der_k(𝒪_X, 𝒪_X)` additively, by postcomposition with the universal
  derivation `d_{X/k}` of Stacks 04CT (`AlgebraicGeometry.Space.differentialsHomAddEquiv`).

## The four terms

`NL_{X/k}` is the naive cotangent complex `AlgebraicGeometry.Space.naiveCotangentComplex` of
Stacks 0D0V at the structure morphism `X ⟶ Spec k`; its sections live one universe above the
structure rings, and so does the coefficient `𝒪_X` of its `Ext` groups
(`AlgebraicGeometry.Space.naiveCotangentCoefficient`).  `Ω_{X/k}` is the sheaf of differentials
`AlgebraicGeometry.Space.sheafOfDifferentials` of Stacks 04CT and `Der_k(𝒪_X, 𝒪_X)` is
`Deformation.Examples.SpaceDerivations`, the derivations of `𝒪_X` over the inverse image of
`𝒪_{Spec k}`.  The derived category is any model of the derived category of `𝒪_X`-modules.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The first display of [Stacks Project, Tag 0E41].**  In Example 0E3Z, let `X` be an
algebraic space over the field `k`.  Then

`Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`,

given as the identifications of those four groups.  `Inf(𝓓_X)` is the infinitesimal
automorphism group `Deformation.infinitesimalAutomorphismGroup` of [Stacks Project, Tag 06JS] of
the deformation category of `X`, a predeformation category
(`Deformation.Examples.isPredeformationCategory_spaceDeformationProjection`), formed at an
arbitrary point `x₀` over `k`, an arbitrary pushforward `i : x₀ ⟶ xε` of it along a dual-number
pair `k → k[ε] → k` — the automorphisms of the deformation `X'` of `X` over `k[ε]` (the trivial
one, `X ×_{Spec k} Spec k[ε]`) which are the identity modulo `ε`.

`k` acts on `𝒪_X`-modules, and so on `Ext⁰`, on `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` and on
`Der_k(𝒪_X, 𝒪_X)`, through the pullback of functions along the structure morphism `X ⟶ Spec k`
(`Deformation.Examples.spaceResidueFieldRingHom`).

* The first component identifies `Inf(𝓓_X)` with `Der_k(𝒪_X, 𝒪_X)` as **groups**, composition of
  automorphisms corresponding to addition of derivations; through the other two it is
  `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)`.
* The second is `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, `k`-linearly, from
  `H⁰(NL_{X/k}) = Ω_{X/k}` (Stacks 0D0Y).
* The third is `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`, `k`-linearly, postcomposition with
  the universal derivation of Stacks 04CT, as Modules on Sites, Definition 04BN defines `Ω`. -/
@[stacks 0E41 "first display: for an algebraic space X over the field k, Inf(Def_X) = \
Ext^0(NL_{X/k}, O_X) = Hom(Omega_{X/k}, O_X) = Der_k(O_X, O_X), as three identifications at every \
point x0 over k and every pushforward x0 -> x_eps along a dual-number pair (06JS): Inf(Def_X) is \
isomorphic as a group to Der_k(O_X, O_X), Ext^0 out of the naive cotangent complex is k-linearly \
Hom(Omega_{X/k}, O_X), and Hom(Omega_{X/k}, O_X) is k-linearly Der_k(O_X, O_X), k acting through \
the structure morphism X -> Spec k. The second display, T Def_X = Ext^1(NL_{X/k}, O_X), is \
registered separately"]
def spaceInfinitesimalAutomorphismGroupChain
    [HasDerivedCategory.{w} (NaiveCotangentModules B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))]
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    letI := naiveCotangentModulesLinear B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    letI := modulesLinearOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    (infinitesimalAutomorphismGroup
        (isPredeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK) g e hpair i hi ≃*
      Multiplicative (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK))) ×
    (DerivedCategory.Ext (DerivedCategory.Q.obj (naiveCotangentComplex B (Spec (.of Λ)) hΛ
        (spaceStructureMap B hΛ hSpec X hX toK)))
        ((DerivedCategory.singleFunctor _ 0).obj
          (naiveCotangentCoefficient B (Spec (.of Λ)) hΛ
            (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))) 0 ≃ₗ[k]
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK) ⟶
        spaceStructureModule B hΛ (spaceOf B hΛ X hX))) ×
    ((sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK) ⟶
        spaceStructureModule B hΛ (spaceOf B hΛ X hX)) ≃ₗ[k]
      SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
  ⟨spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i _ hi,
    naiveCotangentExtZeroLinearEquivDifferentialsHom B (Spec (.of Λ)) hΛ _ _ _,
    differentialsHomLinearEquiv B (Spec (.of Λ)) hΛ _ _ _⟩

end Deformation.Examples

end
