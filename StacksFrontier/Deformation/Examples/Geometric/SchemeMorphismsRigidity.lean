module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsDerivations
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.EquivalenceCriterion

/-!
# Vanishing infinitesimal automorphisms of the deformations of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k` with
`Der_k(𝒪_X, 𝒪_X) = Der_k(𝒪_Y, 𝒪_Y) = 0`. Then the infinitesimal automorphisms of the deformation
category `Def_{X → Y}` of Example 0E3T vanish. This is the step of the proof of Stacks 0ET6
which the source deduces from the exact sequence of Stacks 0E3V and from Stacks 0DY9: an
infinitesimal automorphism of a deformation of `f` is a pair of automorphisms of the deformations
of `X` and of `Y` which are the identity on the special fibres, and by Stacks 0DY9 those
correspond to derivations of `𝒪_X` and of `𝒪_Y`.

## Main results

* `Deformation.Examples.schemeDeformation_hom_eq_id`: an endomorphism of a first-order
  deformation of a scheme without nonzero derivations which lies over the identity is the
  identity.
* `Deformation.Examples.schemeMorphismDeformation_hom_eq_id_of_derivations`: an endomorphism of
  an object of `Def_{X → Y}` over a first-order base which lies over the identity is the
  identity.
* `Deformation.Examples.infinitesimalAutomorphisms_schemeMorphismDeformation_eq_bot`: the
  infinitesimal automorphisms of `Def_{X → Y}` vanish.

## Implementation notes

`Der_k(𝒪_X, 𝒪_X)` is `Deformation.Examples.schemeMorphismDerivations (𝟙 X) pX`, the
derivations of `𝒪_X` over `k` with values in the pushforward of `𝒪_X` along the identity, as in
the first display of Stacks 0DY9. The bijection between such derivations and the self-maps of a
first-order deformation fixing the special fibre is
`Deformation.Examples.deformationSelfMapsEquivDerivations`; vanishing of the derivations makes
every such self-map the identity.

The source and target components of a deformation of `f` are read as deformations of `X` and of
`Y` in the sense of Example 0DY7 through the two endpoint-forgetting functors of Stacks 0E3V,
`Deformation.Examples.schemeMorphismSourceForgetful` and
`Deformation.Examples.schemeMorphismTargetForgetful`.

## References

* [Stacks Project, Tag 0ET6](https://stacks.math.columbia.edu/tag/0ET6)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **A self-map of a first-order deformation fixing the special fibre is the identity** when
the scheme has no nonzero derivations: such self-maps are in bijection with
`Der_k(𝒪_X, 𝒪_X)` by Stacks 0DY9. -/
theorem schemeDeformation_selfMap_eq_id {Z : Over (Spec (.of k))}
    (hZ : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 Z.left) Z.hom))
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) Z)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) (s : P.scheme ⟶ P.scheme)
    (hs : s ≫ P.toBase = P.toBase) (hsp : P.specialMap ≫ s = P.specialMap) : s = 𝟙 P.scheme :=
  congrArg Subtype.val <| (deformationSelfMapsEquivDerivations P coordinate).injective
    (a₁ := ⟨s, hs, hsp⟩) (a₂ := ⟨𝟙 P.scheme, Category.id_comp _, Category.comp_id _⟩)
    (hZ.elim _ _)

/-- **A self-map of a deformation of a scheme lying over the identity of a first-order base is
the identity** when the scheme has no nonzero derivations. -/
theorem schemeDeformation_hom_eq_id {Z : Over (Spec (.of k))}
    (hZ : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 Z.left) Z.hom))
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) Z)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k) (s : P ⟶ P) (hs : s.base = 𝟙 P.base) :
    s.map = 𝟙 P.scheme := by
  refine schemeDeformation_selfMap_eq_id hZ P coordinate s.map ?_ s.special_compat
  have hw := s.cartesian.w
  rwa [hs, baseSpecMap_id, Category.comp_id] at hw

/-- **Rigidity of first-order deformations in `Def_{X → Y}`.** If
`Der_k(𝒪_X, 𝒪_X) = Der_k(𝒪_Y, 𝒪_Y) = 0`, every endomorphism of an object of `Def_{X → Y}`
over an object of `𝒞_Λ` isomorphic to the dual numbers which lies over the identity of the base
is the identity: its components on the deformations of `X` and of `Y`
(`Deformation.Examples.schemeMorphismSourceForgetful`,
`Deformation.Examples.schemeMorphismTargetForgetful`) are self-maps fixing the special fibres,
hence identities by Stacks 0DY9. -/
theorem schemeMorphismDeformation_hom_eq_id_of_derivations
    (hX : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X) pX))
    (hY : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 Y) pY))
    (P : schemeMorphismDeformationCategory f pX pY hf)
    (coordinate : P.left.base ≃ₐ[Λ] DualNumber k) (a : P ⟶ P)
    (ha : a.left.base = 𝟙 P.left.base) : a = 𝟙 P := by
  have hα : a.left.source = 𝟙 P.left.source :=
    schemeDeformation_hom_eq_id (Z := Over.mk pX) hX _ coordinate
      ((schemeMorphismSourceForgetful f pX pY hf).map a) ha
  have hβ : a.left.target = 𝟙 P.left.target :=
    schemeDeformation_hom_eq_id (Z := Over.mk pY) hY _ coordinate
      ((schemeMorphismTargetForgetful f pX pY hf).map a) ha
  exact Over.OverMorphism.ext (SchemeMorphismFamily.Hom.ext ha hα hβ)

/-- **The infinitesimal automorphisms of `Def_{X → Y}` vanish** when
`Der_k(𝒪_X, 𝒪_X) = Der_k(𝒪_Y, 𝒪_Y) = 0`: this is the step of the proof of Stacks 0ET6 which the
source reads off the exact sequence of Stacks 0E3V and Stacks 0DY9. It holds at every choice of
an object over the residue field, its pushforward to the dual numbers and the dual-number pair:
every automorphism of an object over the dual numbers in its fibre is already the identity. -/
theorem infinitesimalAutomorphisms_schemeMorphismDeformation_eq_bot
    (hX : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X) pX))
    (hY : Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 Y) pY))
    (hp : IsCofiberedInGroupoids (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber A₀}
    {xε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber Aε}
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (schemeMorphismDeformationCategoryProjection f pX pY hf).IsHomLift g i) :
    infinitesimalAutomorphisms hp g e hpair i hi = ⊥ := by
  obtain ⟨-, iε, -, -, -⟩ := hpair
  rw [Subgroup.eq_bot_iff_forall]
  intro a _
  obtain ⟨y, rfl⟩ := xε
  exact Iso.ext <| Functor.Fiber.hom_ext <|
    schemeMorphismDeformation_hom_eq_id_of_derivations f pX pY hf hX hY y iε a.hom.1
      (map_eq_id_of_isHomLift_id a.hom.1 a.hom.2)

end Deformation.Examples

end
