module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Deformation.Examples.Geometric.SchemesFiniteDimensional
public import StacksFrontier.Deformation.Schlessinger.DeformationCategoryHull
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquivExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Hull and prorepresentability for the deformations of a proper scheme

Let `k` be a field, `X` a proper scheme over `k`, and `Λ` a Noetherian complete local ring with
residue field `k` (the classical case). The functor

`F : 𝒞_Λ → Sets, A ↦ Ob(Def_X(A))/≅`

of isomorphism classes of deformations of `X` has a hull, and if
`Der_k(𝒪_X, 𝒪_X) = 0` it is prorepresentable. This is [Stacks Project, Tag 0ET5].

## Main results

* `Deformation.Examples.infinitesimalAutomorphisms_schemeDeformation_eq_bot`: the
  infinitesimal automorphisms of `Def_X` vanish when `Der_k(𝒪_X, 𝒪_X) = 0` (first display of
  Stacks 0DY9).
* `Deformation.Examples.exists_hull_isomorphismClasses_scheme`: **Stacks 0ET5**, the hull.
* `Deformation.Examples.isProrepresentableULift_isomorphismClasses_scheme`: **Stacks 0ET5**,
  prorepresentability when `Der_k(𝒪_X, 𝒪_X) = 0`.

## Implementation notes

`Def_X` is `Deformation.Examples.schemeDeformationCategoryProjection X` of Stacks 0DY7, a
deformation category by Stacks 0DY8; `F` is its functor of fibrewise isomorphism classes
`Deformation.isomorphismClasses`. The proof is the source's: Stacks 0DY8 and 0DYA together with
Stacks 06J7 and 06IZ give the hull; when `Der_k(𝒪_X, 𝒪_X) = Inf(Def_X)` vanishes (Stacks 0DY9),
`Def_X` and `F` are equivalent (Stacks 06K0), so `F` is a deformation functor with
finite-dimensional tangent space and Stacks 06JM applies. The general steps are in
`StacksFrontier.Deformation.Schlessinger.DeformationCategoryHull`.

`Der_k(𝒪_X, 𝒪_X)` is `Deformation.Examples.schemeMorphismDerivations (𝟙 X.left) X.hom`, as in
the first display of Stacks 0DY9. The classical case is `Deformation.IsClassical Λ k`.
Prorepresentability is stated as `Deformation.IsProrepresentableULift`, because the values of `F`
lie in the universe of schemes over `𝒞_Λ`, one above the morphism universe of `𝒞_Λ`.

## References

* [Stacks Project, Tag 0ET5](https://stacks.math.columbia.edu/tag/0ET5)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0DYA](https://stacks.math.columbia.edu/tag/0DYA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The infinitesimal automorphisms of `Def_X` vanish when `Der_k(𝒪_X, 𝒪_X) = 0`**: by the
first display of Stacks 0DY9 the group `Inf(Def_X)`, formed at the trivial deformation
`X ×_{Spec k} Spec k[ε]`, is isomorphic to `Der_k(𝒪_X, 𝒪_X)`. -/
theorem infinitesimalAutomorphisms_schemeDeformation_eq_bot
    (X : Over (Spec (CommRingCat.of k)))
    (hDer : ∀ D : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom, D = 0) :
    infinitesimalAutomorphisms
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ)
          X).predeformation.cofibered
        (x₀ := residueTrivialFiberObj X) (xε := dualNumbersTrivialFiberObj X)
        dualNumbersInclusion.{u, u, u}
        (residueMorphism.{u, u, u} (artinianDualNumbers.{u, u, u} Λ k))
        isCanonicalDualNumberPair_dualNumbersInclusion.{u, u, u}
        (dualNumbersTrivialDeformationHom X) (dualNumbersTrivialDeformationHom_isHomLift X) =
      ⊥ := by
  have hs : Subsingleton
      (Multiplicative (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom)) :=
    ⟨fun x y => Multiplicative.toAdd.injective ((hDer _).trans (hDer _).symm)⟩
  have :=
    (infinitesimalAutomorphismGroupTrivialDeformationChain (Λ := Λ) X).1.injective.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

/-- **Stacks Project, Tag 0ET5**, the hull. Let `X` be a proper scheme over the field `k` and
let `Λ` be a Noetherian complete local ring with residue field `k` (the classical case). Then the
functor `F : 𝒞_Λ → Sets, A ↦ Ob(Def_X(A))/≅` of isomorphism classes of deformations of `X` has
a hull: a versal formal object of `F` whose differential is bijective.

`Def_X` is a deformation category by Stacks 0DY8 and its tangent space is finite dimensional by
Stacks 0DYA (`Deformation.Examples.finiteDimensional_schemeTangentSpace`), so Stacks 06J7 and
06IZ give the hull. -/
@[stacks 0ET5 "the hull: for X proper over k and Λ a complete local ring with residue field k, \
the functor A ↦ Ob(Def_X(A))/≅ of isomorphism classes of deformations of X has a hull"]
theorem exists_hull_isomorphismClasses_scheme (hΛ : IsClassical Λ k)
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] :
    let F := isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsHull (categoryOfElements_projection_isCofibered F) ξ :=
  exists_hull_isomorphismClasses_of_isDeformationCategory hΛ (schemeDeformationBased (Λ := Λ) X)
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X)
    (finiteDimensional_schemeTangentSpace X)

/-- **Stacks Project, Tag 0ET5**, prorepresentability. Let `X` be a proper scheme over the field
`k` and let `Λ` be a Noetherian complete local ring with residue field `k`. If
`Der_k(𝒪_X, 𝒪_X) = 0`, then the functor `F : 𝒞_Λ → Sets, A ↦ Ob(Def_X(A))/≅` is
prorepresentable.

By the first display of Stacks 0DY9, `Inf(Def_X) = Der_k(𝒪_X, 𝒪_X)` vanishes
(`Deformation.Examples.infinitesimalAutomorphisms_schemeDeformation_eq_bot`), so `Def_X` and `F`
are equivalent (Stacks 06K0) and `F` is a deformation functor with finite-dimensional tangent
space (Stacks 0DYA); Schlessinger's theorem, Stacks 06JM, applies. Prorepresentability is stated
in the universe-raised form `Deformation.IsProrepresentableULift`, the values of `F` lying one
universe above the morphisms of `𝒞_Λ`. -/
@[stacks 0ET5 "prorepresentability: for X proper over k and Λ a complete local ring with \
residue field k, if Der_k(O_X, O_X) = 0 then the functor A ↦ Ob(Def_X(A))/≅ is prorepresentable",
  sga "7 X 2.27" "more general"]
theorem isProrepresentableULift_isomorphismClasses_scheme (hΛ : IsClassical Λ k)
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (hDer : ∀ D : schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom, D = 0) :
    IsProrepresentableULift
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)) :=
  isProrepresentableULift_isomorphismClasses_of_infinitesimalAutomorphisms_eq_bot hΛ
    (schemeDeformationBased (Λ := Λ) X)
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X)
    (finiteDimensional_schemeTangentSpace X)
    _ _ _ _ _ (infinitesimalAutomorphisms_schemeDeformation_eq_bot X hDer)

end Deformation.Examples

end
