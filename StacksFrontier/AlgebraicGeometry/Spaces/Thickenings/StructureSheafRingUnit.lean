module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The structure sheaf of a thickening read on the smaller site

Let `i : Z ⟶ X` be the inclusion of a thickening of algebraic spaces over a scheme `S`.  The
direct image of sheaves of sets along `i` is an equivalence of categories — it is fully faithful
because `i` is a closed immersion, by [Stacks Project, Tag 04E5], part (1), and essentially
surjective because `Z ⊂ X` is a thickening, by
`AlgebraicGeometry.Space.essSurj_smallEtalePushforward_of_isThickening`.  So the unit
`O ⟶ i_*i^{-1}O` of the adjunction `i^{-1} ⊣ i_*` is an isomorphism at every sheaf, and the same
is therefore true of the unit of the ring-level adjunction of
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction`: a sheaf of rings on the small étale site
of `X` is the direct image of a sheaf of rings on the small étale site of `Z`, canonically.

This is the half of [Stacks Project, Tag 05ZM] which lets the two comorphisms of two morphisms
agreeing on a thickening be compared.  Two morphisms `a, b : X ⟶ W` with `i ≫ a = i ≫ b` have
comorphisms `a^♯ : 𝒪_W ⟶ a_*𝒪_X` and `b^♯ : 𝒪_W ⟶ b_*𝒪_X` with *different* targets; carrying
`𝒪_X` to `i_*(i^{-1}𝒪_X)` by the unit replaces both targets by direct images along the composite
`i ≫ a = i ≫ b` of one and the same sheaf of rings `i^{-1}𝒪_X` on the site of `Z`, and no
comparison of the two direct images has to be chosen.

## Main definitions

* `AlgebraicGeometry.Space.structureRingSheafInverseImage`: the inverse image `f^{-1}𝒪_Y` of the
  structure sheaf of the target, as a sheaf of (not necessarily commutative) rings, the
  coefficient category in which the sheaves of modules of this development are indexed.
* `AlgebraicGeometry.Space.structureSharpRingInverseImage`: the inverse-image form
  `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of the structure map of [Stacks Project, Tag 03G8] at that
  coefficient category, the adjunct of `AlgebraicGeometry.Space.structureSharp`.

## Main results

* `AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage`: the two forms of
  the structure map are adjunct, that is `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` is the unit followed by the direct
  image of `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`.  This is the equation through which a statement about the
  direct-image form becomes one about the inverse-image form.
* `AlgebraicGeometry.Space.ringFsharp_eq_structureSharp` and
  `AlgebraicGeometry.Space.fSharpInverseImage_eq_structureSharpRingInverseImage`: the
  inverse-image form defined here is the one the four-field morphism of small étale ringed
  topoi carries, so that the direct image of sheaves of modules — which is restriction of
  scalars along that form followed by the direct image — is expressed by it.
* `AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening`: **the unit of `i^{-1} ⊣ i_*` at a
  sheaf of rings is an isomorphism for the inclusion of a thickening.**
* `AlgebraicGeometry.Space.isIso_commRingUnit_of_isThickening`: the same at a sheaf of
  *commutative* rings, which is the coefficient category in which
  `AlgebraicGeometry.RingedToposHom.fSharp` takes its values, so that the identification is
  available to a morphism of ringed topoi and not only to the sheaves of modules.

## Implementation notes

The unit is invertible as a morphism of sheaves of rings because it is invertible on the
underlying sheaves of sets and `CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)`
reflects isomorphisms.  Its underlying morphism of sheaves of sets is the unit of the adjunction
of the morphism of topoi, by
`Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit`, so nothing beyond the set-level
statement is needed; and that statement is
`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage` at a direct image which is fully
faithful and essentially surjective.

The inverse-image form of the structure map is defined here at `RingCat` rather than taken from
`AlgebraicGeometry.Space.structureSharpInverseImage`, which is the same map at `CommRingCat`:
the sheaves of modules of this development are indexed over `RingCat`-valued sheaves of rings,
so an ambient sheaf of rings in which a difference of two comorphisms is to be formed has to be
`RingCat`-valued.  No commutativity is lost — the sections of the two agree — and
`AlgebraicGeometry.Space.structureSharp` is itself `RingCat`-valued.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5), part (1).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), the adjunction at an
  algebraic structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The inverse image of the structure sheaf as a sheaf of rings -/

/-- The inverse image `f^{-1}𝒪_Y` of the structure sheaf of the target of a morphism of
algebraic spaces, as a sheaf of rings on the small étale site of the source.  This is
`AlgebraicGeometry.Space.inverseImageStructureSheaf` at the coefficient category in which the
sheaves of modules of this development are indexed; see the implementation notes. -/
noncomputable abbrev structureRingSheafInverseImage (f : X ⟶ Y) :=
  pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
    (smallToposMorphismTypeU B S hS f).inverseImage (structureRingSheaf B S hS Y)

/-- **The inverse-image form `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of the structure map of
[Stacks Project, Tag 03G8]**, as a morphism of sheaves of rings: the adjunct of
`AlgebraicGeometry.Space.structureSharp` along the ring-level adjunction
`f^{-1} ⊣ f_*` of `Stacks.Sheaves.ToposPushforward.ringImageAdjunction`. -/
noncomputable def structureSharpRingInverseImage (f : X ⟶ Y) :
    structureRingSheafInverseImage B S hS f ⟶ structureRingSheaf B S hS X :=
  ((ringImageAdjunction (smallToposMorphismTypeU B S hS f)).homEquiv
    (structureRingSheaf B S hS Y) (structureRingSheaf B S hS X)).symm (structureSharp B S hS f)

/-- **The two forms of the structure map are adjunct.**  The direct-image form
`f^♯ : 𝒪_Y ⟶ f_*𝒪_X` of [Stacks Project, Tag 03G8] is the unit of `f^{-1} ⊣ f_*` followed by
the direct image of the inverse-image form. -/
theorem ringUnit_comp_map_structureSharpRingInverseImage (f : X ⟶ Y) :
    ringUnit (smallToposMorphismTypeU B S hS f) (structureRingSheaf B S hS Y) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS f)).map
          (structureSharpRingInverseImage B S hS f) =
      structureSharp B S hS f :=
  (ringImageAdjunction_homEquiv_apply (smallToposMorphismTypeU B S hS f)
      (structureRingSheaf B S hS Y) (structureRingSheaf B S hS X)
      (structureSharpRingInverseImage B S hS f)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-! ### The inverse-image form is the one the direct image of modules is built from -/

/-- **The ring-level direct-image form of the structure map of
`AlgebraicGeometry.RingedToposHom.ringFsharp` is `AlgebraicGeometry.Space.structureSharp`.**
Both are morphisms of sheaves of rings `𝒪_Y ⟶ f_*𝒪_X`, and both have the transpose of the
inverse-image form of [Stacks Project, Tag 03G8] for their underlying morphism of sheaves of
sets, by `Stacks.Sheaves.RingedToposModules.RingedToposHom.ringSheafMap_ringFsharp` and by
`AlgebraicGeometry.Space.homEquiv_structureSharpInverseImageSet`. -/
theorem ringFsharp_eq_structureSharp (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).ringFsharp = structureSharp B S hS f := by
  refine (sheafCompose (SmallEtale.topology B S hS Y.1)
    (CategoryTheory.forget RingCat.{u})).map_injective ?_
  refine ((smallEtaleRingedToposHom B S hS f).ringSheafMap_ringFsharp).trans ?_
  exact homEquiv_structureSharpInverseImageSet B S hS f

/-- **The inverse-image form of the structure map carried by the four-field morphism of small
étale ringed topoi is `AlgebraicGeometry.Space.structureSharpRingInverseImage`.**  Both are
transposes of the same morphism `𝒪_Y ⟶ f_*𝒪_X` along the ring-level adjunction `f^{-1} ⊣ f_*`,
by `AlgebraicGeometry.Space.ringFsharp_eq_structureSharp`, and the transposition is a
bijection.

This is what identifies the ideal of the thickening read on the smaller site, which the direct
image of modules of `Stacks.Sheaves.RingedToposModules.RingedToposHom.pushforwardModules` is
built by restricting scalars along, with the map
`AlgebraicGeometry.Space.structureSharpRingInverseImage` that the rest of this development
uses. -/
theorem fSharpInverseImage_eq_structureSharpRingInverseImage (f : X ⟶ Y) :
    (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage =
      structureSharpRingInverseImage B S hS f :=
  ((Equiv.symm_apply_apply ((ringImageAdjunction (smallToposMorphismTypeU B S hS f)).homEquiv
        (structureRingSheaf B S hS Y) (structureRingSheaf B S hS X))
      (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).symm).trans
    (congrArg ((ringImageAdjunction (smallToposMorphismTypeU B S hS f)).homEquiv
        (structureRingSheaf B S hS Y) (structureRingSheaf B S hS X)).symm
      (ringFsharp_eq_structureSharp B S hS f))

/-! ### The unit at the inclusion of a thickening -/

variable (Z : ClosedSubspaces B S hS X.1)

/-- The direct image of sheaves of sets along the inclusion of a thickening is an equivalence. -/
private theorem isEquivalence_pushforward_subspaceInclusion (hZ : IsThickening B S hS X Z.1) :
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward.IsEquivalence :=
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS
    (subspaceInclusion B S hS X Z) Z.2.2
  ⟨hff.faithful, hff.full, essSurj_smallEtalePushforward_of_isThickening B S hS Z hZ⟩

/-- **The unit `O ⟶ i_*i^{-1}O` of `i^{-1} ⊣ i_*` at a sheaf of rings is an isomorphism for the
inclusion `i : Z ⟶ X` of a thickening.**  The direct image of sheaves of sets along `i` is fully
faithful because `i` is a closed immersion and essentially surjective because `Z ⊂ X` is a
thickening, so the set-level unit is invertible at every sheaf; and
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)` reflects isomorphisms.

So every sheaf of rings on the small étale site of `X` is canonically the direct image of one
on the small étale site of `Z`.  This is what lets the comorphisms of two morphisms agreeing on
a thickening be read in one and the same sheaf of rings; see the module documentation. -/
@[stacks 05ZM "the structure-sheaf half, at the small étale sites: every sheaf of rings on the \
site of the ambient space — its structure sheaf in particular — is canonically the direct image \
along the inclusion of a sheaf of rings on the site of the thickening, which is the \
identification under which the two topoi carry one and the same structure sheaf"]
theorem isIso_ringUnit_of_isThickening (hZ : IsThickening B S hS X Z.1)
    (O : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) :
    IsIso (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)) O) := by
  have := isEquivalence_pushforward_subspaceInclusion B S hS Z hZ
  have hset : IsIso ((smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS X Z)).adj.unit.app
      ((sheafCompose (SmallEtale.topology B S hS X.1)
        (CategoryTheory.forget RingCat.{u})).obj O)) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj).2
      (Functor.EssSurj.mem_essImage _ _)
  have key := Stacks.Sheaves.RingedToposModules.ringSheafMap_ringUnit
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)) O
  have : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).map
      (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)) O)) :=
    key ▸ hset
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B S hS X.1)
    (CategoryTheory.forget RingCat.{u}))

/-- **The unit of the adjunction of [Stacks Project, Tag 00YV] at a sheaf of *commutative* rings
is an isomorphism for the inclusion `i : Z ⟶ X` of a thickening.**

This is `AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening` at the coefficient category in
which `AlgebraicGeometry.RingedToposHom.fSharp` takes its values, and the proof is the same: the
direct image of sheaves of sets along a thickening is fully faithful and essentially surjective,
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor_isEquivalence` carries that to the
direct image of sheaves of commutative rings, and the unit of an adjunction whose right adjoint
is an equivalence is an isomorphism.

Stated at `CommRingCat` the identification applies to a morphism of ringed topoi: the
invertibility of a structure map is the hypothesis `[IsIso f.fSharp]` of
`AlgebraicGeometry.RingedToposHom.inverse`, and
`AlgebraicGeometry.RingedToposHom.ofInverseImageIso` builds a morphism of ringed topoi out of a
morphism of topoi together with an isomorphism of inverse-image structure sheaves. -/
@[stacks 05ZM "the structure-sheaf half at the coefficient category of a morphism of ringed \
topoi: the direct image along the inclusion identifies the sheaves of commutative rings on the \
site of the thickening with those on the site of the ambient space, carrying the inverse image \
of the structure sheaf of the ambient space to that structure sheaf"]
theorem isIso_commRingUnit_of_isThickening (hZ : IsThickening B S hS X Z.1)
    (O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    IsIso ((commRingImageAdjunction
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))).unit.app O) := by
  have := pushforwardCommRingFunctor_isEquivalence
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
    (isEquivalence_pushforward_subspaceInclusion B S hS Z hZ)
  exact (Adjunction.isIso_unit_app_iff_mem_essImage (commRingImageAdjunction
    (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)))).2
    (Functor.EssSurj.mem_essImage _ _)

end AlgebraicGeometry.Space

end
