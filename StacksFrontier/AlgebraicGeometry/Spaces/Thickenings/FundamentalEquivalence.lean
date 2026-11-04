module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafInverseImage

/-!
# The fundamental equivalence of a thickening of algebraic spaces

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`; in the notation of the
source `G` is `X` and the ambient space `X` is `X'`. The spaces-étale sheaf topoi of the two
spaces are canonically equivalent — that is the topos half of Stacks 05ZM, proved as
`AlgebraicGeometry.Space.spacesEtaleSheafEquiv_of_isThickening` — and the structure sheaf
`𝒪_{X'}` of the ambient space may therefore be read as a sheaf of rings on the spaces-étale
site of the closed subspace. The pair so obtained is the right-hand side of equation 76.9.1.2,

`(Sh(X'_{spaces,étale}), 𝒪_{X'}) ≅ (Sh(X_{spaces,étale}), 𝒪_{X'})`,

and this file transports the structure sheaf and proves that equation: the two ringed topoi are
isomorphic, as locally ringed topoi, by the canonical morphism out of an inverse-image ringed
topos.

The transport is the inverse image of `𝒪_{X'}` along the geometric morphism underlying the
equivalence of topoi. So the ringed topos on the right-hand side is the inverse-image ringed
topos of Stacks 04KR, and the comparison of the two sides is its canonical morphism to
`(Sh(X'_{spaces,étale}), 𝒪_{X'})`; the content of the equation is that this comparison is an
isomorphism of locally ringed topoi, which is the conjunction of: the underlying geometric
morphism is an equivalence in both directions, the structure map `𝒪_{X'} ⟶ f_*𝒪_{X'}` is
invertible, and the comparison is a morphism of locally ringed topoi.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleToposHom_of_isThickening`: the geometric morphism
  `Sh(X_{spaces,étale}) ⟶ Sh(X'_{spaces,étale})` underlying the equivalence of topoi of
  Stacks 05ZM.
* `AlgebraicGeometry.Space.subspaceRingedTopos_of_isThickening`: the ringed topos
  `(Sh(X_{spaces,étale}), 𝒪_{X'})`, the right-hand side of equation 76.9.1.2.
* `AlgebraicGeometry.Space.ambientStructureSheaf_of_isThickening`: its structure sheaf, namely
  `𝒪_{X'}` read as a sheaf of rings on the spaces-étale site of the closed subspace.
* `AlgebraicGeometry.Space.spacesEtaleRingedToposHom_of_isThickening`: the canonical morphism
  of ringed topoi from `(Sh(X_{spaces,étale}), 𝒪_{X'})` to `(Sh(X'_{spaces,étale}), 𝒪_{X'})`.

## Main results

* `AlgebraicGeometry.Space.fundamentalEquivalence_of_isThickening`: **Stacks 05ZM**, equation
  76.9.1.2. That canonical morphism is an isomorphism of locally ringed topoi.
* `AlgebraicGeometry.Space.fSharpInverseImage_spacesEtaleRingedToposHom_of_isThickening`: its
  structure map, in inverse-image form, is the identity of `𝒪_{X'}` — the transported sheaf is
  the inverse image of `𝒪_{X'}` on the nose, not merely isomorphic to it.

## Implementation notes

Nothing about the structure sheaf is re-proved here. The geometric morphism is read off the
equivalence of topoi, whose quasi-inverse is its direct image and whose functor is its inverse
image, left exact because an equivalence preserves all limits. Everything else is the general
theory of an inverse-image ringed topos: `AlgebraicGeometry.inverseImageRingedTopos` carries
the transported structure sheaf, `AlgebraicGeometry.inverseImageRingedToposHom` is the
comparison, its inverse-image structure map is the identity by
`AlgebraicGeometry.inverseImageRingedToposHom_fSharpInverseImage`, and it is a morphism of
locally ringed topoi by `AlgebraicGeometry.inverseImageRingedToposHom_isLocallyRinged`, which
is Stacks 04KR. The one thing left to check is invertibility of the direct-image form of the
structure map, and that holds because the structure map is the unit of the adjunction between
the inverse image and the direct image of sheaves of commutative rings, which forgetting the
ring operations carries to the unit of `f⁻¹ ⊣ f_*` on sheaves of sets
(`Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app`); that unit
is invertible because the inverse image is fully faithful, and forgetting the ring operations
reflects isomorphisms.

The generality is that of the topos half: an arbitrary thickening, not merely a first-order
one. The equivalence of spaces-étale *sites* of
`AlgebraicGeometry.Space.spacesEtaleEquivalenceOfIsFirstOrderThickening` is available only in
the first-order case, so the geometric morphism here is not presented by a functor of sites and
`AlgebraicGeometry.RingedToposSiteHom` is not the right notion; the comparison is a
`AlgebraicGeometry.RingedToposHom`, which takes an arbitrary geometric morphism.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### The geometric morphism underlying the equivalence of topoi -/

/-- **The geometric morphism of a thickening on the spaces-étale topoi.** For a thickening
`G ⊂ X` of algebraic spaces over `S` the equivalence of spaces-étale sheaf topoi of
Stacks 05ZM, read as a morphism of topoi `Sh(G_{spaces,étale}) ⟶ Sh(X_{spaces,étale})`: its
direct image is the quasi-inverse of the equivalence and its inverse image is the equivalence
itself, which is left exact because an equivalence of categories preserves all limits. -/
noncomputable abbrev spacesEtaleToposHom_of_isThickening (hG : IsThickening B S hS X G) :
    MorphismOfTopoi
      (Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG)) (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))) where
  pushforward := (spacesEtaleSheafEquiv_of_isThickening B S hS hG).inverse
  inverseImage := (spacesEtaleSheafEquiv_of_isThickening B S hS hG).functor
  adj := (spacesEtaleSheafEquiv_of_isThickening B S hS hG).toAdjunction
  preservesFiniteLimits := inferInstance

/-- The direct image of the geometric morphism of a thickening is an equivalence, being the
quasi-inverse of the equivalence of topoi of Stacks 05ZM. -/
instance isEquivalence_pushforward_spacesEtaleToposHom_of_isThickening
    (hG : IsThickening B S hS X G) :
    (spacesEtaleToposHom_of_isThickening B S hS hG).pushforward.IsEquivalence :=
  inferInstanceAs
    (Functor.IsEquivalence (spacesEtaleSheafEquiv_of_isThickening B S hS hG).inverse)

/-! ### The transported structure sheaf and the two ringed topoi -/

/-- **The right-hand side of equation 76.9.1.2.** The spaces-étale sheaf topos of the closed
subspace of a thickening `G ⊂ X`, equipped with the structure sheaf of the *ambient* space
transported along the equivalence of topoi: in the notation of the source, the ringed topos
`(Sh(X_{spaces,étale}), 𝒪_{X'})`. -/
noncomputable abbrev subspaceRingedTopos_of_isThickening (hG : IsThickening B S hS X G) :
    RingedTopos :=
  inverseImageRingedTopos (SpacesEtale B S hS (IsThickening.space B S hS hG))
    (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
    (spacesEtaleRingedTopos B S hS X) (spacesEtaleToposHom_of_isThickening B S hS hG)

/-- **`𝒪_{X'}` read as a sheaf on `X_{spaces,étale}`.** The structure sheaf of the ambient space
of a thickening `G ⊂ X`, transported to the spaces-étale site of the closed subspace along the
equivalence of topoi of Stacks 05ZM: its inverse image under the geometric morphism of the
thickening. -/
noncomputable abbrev ambientStructureSheaf_of_isThickening (hG : IsThickening B S hS X G) :
    Sheaf (SpacesEtale.topology B S hS (IsThickening.space B S hS hG)) CommRingCat.{u + 1} :=
  (subspaceRingedTopos_of_isThickening B S hS hG).O

/-- **The comparison of the two sides of equation 76.9.1.2.** The canonical morphism of ringed
topoi from `(Sh(X_{spaces,étale}), 𝒪_{X'})` to `(Sh(X'_{spaces,étale}), 𝒪_{X'})`: the
geometric morphism of the thickening together with the unit of the adjunction between the
inverse image and the direct image of sheaves of commutative rings. This is the canonical
morphism of Stacks 04KR out of an inverse-image ringed topos. -/
noncomputable def spacesEtaleRingedToposHom_of_isThickening (hG : IsThickening B S hS X G) :
    RingedToposHom (subspaceRingedTopos_of_isThickening B S hS hG)
      (spacesEtaleRingedTopos B S hS X) :=
  inverseImageRingedToposHom (SpacesEtale B S hS (IsThickening.space B S hS hG))
    (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
    (spacesEtaleRingedTopos B S hS X) (spacesEtaleToposHom_of_isThickening B S hS hG)

/-- The geometric morphism underlying the comparison is the geometric morphism of the
thickening. -/
@[simp]
theorem spacesEtaleRingedToposHom_of_isThickening_toToposHom (hG : IsThickening B S hS X G) :
    (spacesEtaleRingedToposHom_of_isThickening B S hS hG).toToposHom =
      spacesEtaleToposHom_of_isThickening B S hS hG := rfl

/-- The structure map of the comparison is the unit of the adjunction between the inverse image
and the direct image of sheaves of commutative rings. -/
@[simp]
theorem spacesEtaleRingedToposHom_of_isThickening_fSharp (hG : IsThickening B S hS X G) :
    (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharp =
      (commRingImageAdjunction (spacesEtaleToposHom_of_isThickening B S hS hG)).unit.app
        (spacesEtaleRingedTopos B S hS X).O := rfl

/-- **The transported structure sheaf is `𝒪_{X'}` on the nose.** The structure map of the
comparison, in inverse-image form, is the identity of `𝒪_{X'}`: the structure sheaf of the
ringed topos `(Sh(X_{spaces,étale}), 𝒪_{X'})` *is* the inverse image of `𝒪_{X'}`, not merely
isomorphic to it. -/
theorem fSharpInverseImage_spacesEtaleRingedToposHom_of_isThickening
    (hG : IsThickening B S hS X G) :
    (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharpInverseImage =
      𝟙 ((inverseImageCommRingFunctor (spacesEtaleToposHom_of_isThickening B S hS hG)).obj
        (spacesEtaleRingedTopos B S hS X).O) :=
  inverseImageRingedToposHom_fSharpInverseImage
    (SpacesEtale B S hS (IsThickening.space B S hS hG))
    (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
    (spacesEtaleRingedTopos B S hS X) (spacesEtaleToposHom_of_isThickening B S hS hG)

/-- The structure map of the comparison is invertible.

Forgetting the ring operations carries it to the unit of `f⁻¹ ⊣ f_*` on sheaves of sets, which
is invertible because the inverse image — the equivalence of topoi of Stacks 05ZM — is fully
faithful; and forgetting the ring operations reflects isomorphisms. -/
instance isIso_fSharp_spacesEtaleRingedToposHom_of_isThickening
    (hG : IsThickening B S hS X G) :
    IsIso (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharp := by
  have hunit : (spacesEtaleRingedTopos B S hS X).forgetRing.map
      (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharp =
      (spacesEtaleToposHom_of_isThickening B S hS hG).adj.unit.app
        ((spacesEtaleRingedTopos B S hS X).forgetRing.obj
          (spacesEtaleRingedTopos B S hS X).O) :=
    forgetRing_map_commRingImageAdjunction_unit_app (spacesEtaleRingedTopos B S hS X)
      (spacesEtaleToposHom_of_isThickening B S hS hG)
  have : IsIso ((spacesEtaleRingedTopos B S hS X).forgetRing.map
      (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharp) := by
    rw [hunit]
    exact inferInstanceAs (IsIso
      ((spacesEtaleSheafEquiv_of_isThickening B S hS hG).toAdjunction.unit.app
        ((spacesEtaleRingedTopos B S hS X).forgetRing.obj
          (spacesEtaleRingedTopos B S hS X).O)))
  exact isIso_of_reflects_iso _ (spacesEtaleRingedTopos B S hS X).forgetRing

/-! ### Equation 76.9.1.2 -/

/-- **Stacks 05ZM, equation 76.9.1.2.** Let `G ⊂ X` be a thickening of algebraic spaces over a
scheme `S`; in the notation of the source `G` is `X` and `X` is `X'`. Then

`(Sh(X'_{spaces,étale}), 𝒪_{X'}) ≅ (Sh(X_{spaces,étale}), 𝒪_{X'})`

as locally ringed topoi, the right-hand structure sheaf being `𝒪_{X'}` transported along the
equivalence of spaces-étale topoi. The isomorphism is the canonical morphism
`AlgebraicGeometry.Space.spacesEtaleRingedToposHom_of_isThickening`, and the four conjuncts
below are what make it one: its geometric morphism is an equivalence in both directions, its
structure map is invertible, and it is a morphism of locally ringed topoi. -/
@[stacks 05ZM]
theorem fundamentalEquivalence_of_isThickening (hG : IsThickening B S hS X G) :
    Functor.IsEquivalence
        (spacesEtaleRingedToposHom_of_isThickening B S hS hG).toToposHom.pushforward ∧
      Functor.IsEquivalence
        (spacesEtaleRingedToposHom_of_isThickening B S hS hG).toToposHom.inverseImage ∧
      IsIso (spacesEtaleRingedToposHom_of_isThickening B S hS hG).fSharp ∧
      RingedToposHom.IsLocallyRinged
        (spacesEtaleRingedToposHom_of_isThickening B S hS hG) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isEquivalence_pushforward_spacesEtaleToposHom_of_isThickening B S hS hG
  · exact inferInstanceAs
      (Functor.IsEquivalence (spacesEtaleSheafEquiv_of_isThickening B S hS hG).functor)
  · exact inferInstance
  · exact inverseImageRingedToposHom_isLocallyRinged
      (SpacesEtale.topology B S hS (IsThickening.space B S hS hG))
      (spacesEtaleRingedTopos B S hS X) (spacesEtaleToposHom_of_isThickening B S hS hG)

end AlgebraicGeometry.Space

end
