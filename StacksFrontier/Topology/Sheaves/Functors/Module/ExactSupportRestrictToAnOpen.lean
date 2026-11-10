module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportSections
public import StacksFrontier.Topology.Sheaves.RingedSpace.RestrictMorphism

/-!
# A closed quotient morphism of ringed spaces restricts to an open subspace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces — a morphism whose underlying
continuous map is a homeomorphism onto a closed subset and whose comorphism `𝒪_X ⟶ i_* 𝒪_Z` is
locally surjective — and let `U ⊆ X` be open. Then the restriction
`i|_{i⁻¹U} : Z|_{i⁻¹U} ⟶ X|_U` is again a closed quotient morphism of ringed spaces. This file
builds that restricted situation, as
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.restrict`.

Both conditions are local on the target, which is the whole content. The topological one is
`AlgebraicGeometry.RingedSpace.isClosedEmbedding_restrictHom`, already in the library. The one
on the comorphism is proved here: a section of `i_* 𝒪_Z` over an open `W ⊆ U` is a section over
the corresponding open of `X`, and a lift of it on a neighbourhood of a point produced by local
surjectivity on `X` is a lift on a neighbourhood inside `U`, because an open of `X` contained in
`U` is an open of `U`.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.restrict`: **the restricted
  situation**, the closed quotient morphism `i|_{i⁻¹U} : Z|_{i⁻¹U} ⟶ X|_U`.

## Main results

* `Stacks.Cohomology.HigherDirectImage.isLocallySurjective_restrictedMorphism`: local
  surjectivity of the comorphism of a morphism of ringed spaces is inherited by its restriction
  to an open subspace of the target.

## Why this exists

[Stacks, Tag 0E2N] is proved by replacing `X` by an affine open, and its canonical map
`Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap` is attached to a closed quotient
morphism of ringed spaces. Naming the map of the restricted situation therefore presupposes that
a closed quotient morphism restricts, which is what is built here. The comparison of
`R ℰom(𝒪_Z, -)` with restriction is built on top of this, in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportRestrictComparison.lean`;
it is not proved to be an isomorphism, and the identification of the restriction of
`tensorDerivedSheafHomMap` with the map of the restricted situation is not anywhere. What is
proved towards invertibility is the reduction to a statement after `(i|_{i⁻¹U})_*`, in
`ExactSupportRestrictComparisonIso.lean` (beside the comparison file just named),
and the descent half of it, now as an isomorphism of functors — `moduleDescend` commutes with
restriction to `U` — in
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictDescend.lean`, over its
content on sections in
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictSections.lean`. The restricted
situation built here is what both of those are stated against.

## Implementation notes

The restriction of the morphism is `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`,
whose components are written out, rather than the definitionally equal
`AlgebraicGeometry.RingedSpace.restrictHom`
(`Stacks.Cohomology.DerivedRestrictionPullback.restrictHom_eq_restrictedMorphism`): the proof
below rewrites with those components. The closed-embedding field is nonetheless discharged by
the lemma stated for `restrictHom`, the two morphisms being the same term.

Four of the five lemmas below hold by `rfl` and exist only to put the maps that occur in the
proof into one spelling. Sections of the structure sheaf of an open subspace are sections of the
structure sheaf of the ambient space over the image open, definitionally but not syntactically,
and the elaborated goal mixes the two spellings; `rw` and `simp` match below default
transparency and do not cross them, so each crossing is paid once, in a `rfl` lemma, and the
section itself is retyped by `change` at the point in the proof where both the hypothesis and
the goal are already in the ambient spelling. This is the friction the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/KFlatAndDerivedPullback/RestrictionIsPullback.lean`
describe for instance search, met here in rewriting.

The final step compares two composites of restriction maps of `𝒪_Z` between one and the same
pair of opens. The opens of a space form a poset, so the two composites are equal because the
hom type is a subsingleton, and no coherence has to be checked.

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.HigherDirectImage

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- The comorphism of `f|_{f⁻¹V}` on sections over an open `W` of `V`, read in the structure
sheaves of the ambient spaces: it is the comorphism of `f` over the image of `W` in `Y`,
followed by the identification of `f⁻¹` of that open with the image in `X` of the preimage of
`W` under the restricted map. -/
theorem restrictedMorphism_c_app_apply (W : Opens (restrictToOpen Y V).carrier)
    (s : (restrictToOpen Y V).presheaf.obj (op W)) :
    (ConcreteCategory.hom ((restrictedMorphism f V).hom.c.app (op W))) s =
      (ConcreteCategory.hom (X.presheaf.map
        (eqToHom (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W)).op))
        ((ConcreteCategory.hom (f.hom.c.app (op (V.isOpenEmbedding.functor.obj W)))) s) := rfl

/-- Restriction of a section of `(f|_{f⁻¹V})_* 𝒪_{X|_{f⁻¹V}}` along an inclusion of opens of `V`,
read in the structure sheaf of `X`. -/
theorem pushforward_restrict_apply {W₁ W₂ : Opens (restrictToOpen Y V).carrier} (h : W₂ ≤ W₁)
    (t : ((TopCat.Presheaf.pushforward CommRingCat (restrictedMorphism f V).hom.base).obj
      (restrictToOpen X (preimageOpen f V)).presheaf).obj (op W₁)) :
    TopCat.Presheaf.restrictOpen t W₂ h =
      (ConcreteCategory.hom (X.presheaf.map
        ((preimageOpen f V).isOpenEmbedding.functor.map
          ((Opens.map (restrictedMorphismBase f V)).map (homOfLE h))).op)) t := rfl

/-- Restriction of a section of `f_* 𝒪_X` along an inclusion of opens of `Y`, read in the
structure sheaf of `X`. -/
theorem pushforwardAmbient_restrict_apply {U₁ U₂ : Opens Y} (h : U₂ ≤ U₁)
    (t : ((TopCat.Presheaf.pushforward CommRingCat f.hom.base).obj X.presheaf).obj (op U₁)) :
    TopCat.Presheaf.restrictOpen t U₂ h =
      (ConcreteCategory.hom (X.presheaf.map ((Opens.map f.hom.base).map (homOfLE h)).op)) t := rfl

/-- The restriction maps of `f_* 𝒪_X`, read in the structure sheaf of `X`. -/
theorem pushforwardAmbient_map_eq {U₁ U₂ : (Opens Y)ᵒᵖ} (g : U₁ ⟶ U₂) :
    ((TopCat.Presheaf.pushforward CommRingCat f.hom.base).obj X.presheaf).map g =
      X.presheaf.map ((Opens.map f.hom.base).map g.unop).op := rfl

/-- **Local surjectivity of the comorphism is inherited by the restriction to an open subspace
of the target.** If `𝒪_Y ⟶ f_* 𝒪_X` is locally surjective then so is
`𝒪_{Y|_V} ⟶ (f|_{f⁻¹V})_* 𝒪_{X|_{f⁻¹V}}`.

Given a section `t` of the restricted pushforward over an open `W` of `V` and a point `x` of
`W`, the hypothesis applied over the image of `W` in `Y` produces an open `V₀ ∋ x` of `Y`
contained in that image and a lift of `t` over `V₀`. As `V₀ ⊆ V`, it is an open of `V`, it is
contained in `W`, and the lift is a lift over it. -/
theorem isLocallySurjective_restrictedMorphism
    (hf : TopCat.Presheaf.IsLocallySurjective f.hom.c) :
    TopCat.Presheaf.IsLocallySurjective (restrictedMorphism f V).hom.c := by
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hf ⊢
  intro W t x hx
  have hmem : (x.1 : Y.carrier) ∈ V.isOpenEmbedding.functor.obj W := ⟨x, hx, rfl⟩
  have hW := isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W
  obtain ⟨V₀, hV₀, ⟨s, hs⟩, hxV₀⟩ :=
    hf (V.isOpenEmbedding.functor.obj W) (X.presheaf.map (eqToHom hW.symm).op t) x.1 hmem
  have hle : V₀ ≤ V := fun z hz => isOpenEmbeddingFunctor_obj_le V W (hV₀ hz)
  have e : V.isOpenEmbedding.functor.obj ((Opens.map (Opens.inclusion' V)).obj V₀) = V₀ := by
    rw [Opens.functor_map_eq_inf, inf_eq_left]
    exact hle
  have hW'le : (Opens.map (Opens.inclusion' V)).obj V₀ ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hV₀ hz
    exact (Subtype.ext hwz : w = z) ▸ hw
  refine ⟨(Opens.map (Opens.inclusion' V)).obj V₀, hW'le,
    ⟨Y.presheaf.map (eqToHom e).op s, ?_⟩, hxV₀⟩
  rw [pushforward_restrict_apply]
  change X.presheaf.obj (op ((preimageOpen f V).isOpenEmbedding.functor.obj
    ((Opens.map (restrictedMorphismBase f V)).obj W))) at t
  rw [restrictedMorphism_c_app_apply,
    ← ConcreteCategory.comp_apply (Y.presheaf.map (eqToHom e).op), f.hom.c.naturality,
    ConcreteCategory.comp_apply, hs, pushforwardAmbient_restrict_apply,
    pushforwardAmbient_map_eq]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun m => (ConcreteCategory.hom (X.presheaf.map m)) t) (Subsingleton.elim _ _)

end Stacks.Cohomology.HigherDirectImage

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.Cohomology.HigherDirectImage

universe u

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)

/-- **The restricted situation.** A closed quotient morphism of ringed spaces `i : Z ⟶ X`
restricts, along an open `U ⊆ X`, to a closed quotient morphism `Z|_{i⁻¹U} ⟶ X|_U`.

The underlying morphism is `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`; its
underlying continuous map is a homeomorphism onto a closed subset by
`AlgebraicGeometry.RingedSpace.isClosedEmbedding_restrictHom`, and its comorphism is locally
surjective by
`Stacks.Cohomology.HigherDirectImage.isLocallySurjective_restrictedMorphism`. -/
@[reducible]
def restrict : ClosedQuotientMorphismOfRingedSpaces.{u} where
  X := restrictToOpen S.X U
  Z := restrictToOpen S.Z (preimageOpen S.i U)
  i := restrictedMorphism S.i U
  isClosedEmbedding :=
    AlgebraicGeometry.RingedSpace.isClosedEmbedding_restrictHom S.i U S.isClosedEmbedding
  isLocallySurjective :=
    isLocallySurjective_restrictedMorphism S.i U S.isLocallySurjective

/-- The ambient ringed space of the restricted situation is the open subspace `U`. -/
theorem restrict_X : (S.restrict U).X = restrictToOpen S.X U := rfl

/-- The closed ringed subspace of the restricted situation is the open subspace `i⁻¹U` of `Z`. -/
theorem restrict_Z : (S.restrict U).Z = restrictToOpen S.Z (preimageOpen S.i U) := rfl

/-- The morphism of the restricted situation is the restriction of `i`. -/
theorem restrict_i : (S.restrict U).i = restrictedMorphism S.i U := rfl

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
