module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleInverseImageReflectsZero

/-!
# A section of `ε⁻¹F` is locally pulled back from a section over the image open

Let `S` be a scheme contained in a big étale site, let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of Stacks 08H7, and let `F` be
a sheaf of sets on the small Zariski site of `S`.  Then `ε⁻¹F` is the étale sheafification of
`V ↦ F(im V)` — the sections of `F` over the image open of `V`, which is an open because étale
morphisms are open (Stacks 03WT) — so **every section of `ε⁻¹F` over an object `V` of the small
étale site agrees, on a covering sieve of `V`, with the image of a section of `F` over the image
open**.

## Why this is here

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleInverseImageReflectsZero.lean`
builds the comparison `AlgebraicGeometry.SmallEtale.imageOpenToInverseImage` and proves it an
isomorphism for an arbitrary sheaf of sets; what it then needs, and all it names, is the
*injective* half of the comparison with the presheaf `V ↦ F(im V)`, over an open of `S`
(`injective_toSheafify_imageOpenPresheaf`), because zero-detection along `ε` only ever needs
sections to be separated.

The **surjective** half is the half the finite-type converse of Stacks 08HD needs, and it had no
name.  Stacks' proof of that converse descends a finite generating family of `ε^*𝓕` to sections
of `𝓕` over an open of `S`, and the step that produces those sections is exactly this one: a
section of `ε⁻¹𝓕` over an étale `V` is, after shrinking `V`, pulled back from `𝓕(im V)`.  (The
remaining step is the extension of scalars `ε^*𝓕 = 𝒪 ⊗_{ε⁻¹𝒪_S} ε⁻¹𝓕`, whose sections are
locally finite sums of elementary tensors; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteTypeDescent.lean`.)

Nothing here is about modules: the inverse image of a sheaf of modules has the same sections as
the inverse image of the underlying sheaf of sets, by
`Stacks.Sheaves.ToposPullback.pullbackModuleAb`, which is the device
`SmallEtaleInverseImageReflectsZero.lean` already uses to reduce the module statement to the
set-level one.

## Main results

* `AlgebraicGeometry.SmallEtale.imageOpenToInverseImageComp`: the comparison
  `(V ↦ F(im V)) ⟶ ε⁻¹F`, as a map of presheaves of sets.
* `AlgebraicGeometry.SmallEtale.isLocallySurjective_imageOpenToInverseImageComp`: it is locally
  surjective.
* `AlgebraicGeometry.SmallEtale.exists_sieve_imageOpen_section`: the elementwise form — **a
  section of `ε⁻¹F` over `V` is, on a covering sieve of `V`, the image of a section of `F` over
  the image open**.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison `(V ↦ F(im V)) ⟶ ε⁻¹F`**: the sheafification unit of the image-open
sections, followed by the identification of that sheafification with `ε⁻¹F`.  This is
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage` with a general sheaf of sets in place
of the structure sheaf. -/
noncomputable def imageOpenToInverseImageComp
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    imageOpenPresheaf B S hS F ⟶ ((toposInverseImage B S hS).obj F).obj :=
  toSheafify (topology B S hS) (imageOpenPresheaf B S hS F) ≫ imageOpenToInverseImage B S hS F

/-- **`ε⁻¹F` is a sheafification of `V ↦ F(im V)`, surjective half**: the comparison map is
locally surjective, being a sheafification unit composed with an isomorphism. -/
instance isLocallySurjective_imageOpenToInverseImageComp
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    Presheaf.IsLocallySurjective (topology B S hS) (imageOpenToInverseImageComp B S hS F) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (topology B S hS)
    (toSheafify (topology B S hS) (imageOpenPresheaf B S hS F) ≫
      imageOpenToInverseImage B S hS F))

/-- **`ε⁻¹F` is a sheafification of `V ↦ F(im V)`, injective half**, for a general object of the
small étale site.  Over an *open* of `S` the sheafification unit is injective on the nose
(`AlgebraicGeometry.SmallEtale.injective_toSheafify_imageOpenPresheaf`); in general it is only
locally injective, which is what this records. -/
instance isLocallyInjective_imageOpenToInverseImageComp
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    Presheaf.IsLocallyInjective (topology B S hS) (imageOpenToInverseImageComp B S hS F) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (topology B S hS)
    (toSheafify (topology B S hS) (imageOpenPresheaf B S hS F) ≫
      imageOpenToInverseImage B S hS F))

/-- **A section of `ε⁻¹F` over an object of the small étale site is locally pulled back from a
section of `F` over the image open.**  There is a covering sieve of `V` over each member `W` of
which the restricted section is the image of a section of `F` over `im W`.

This is the step of Stacks' proof of the converse of Stacks 08HD that produces the sections
`tᵢ ∈ 𝓕(U)`: the open `U` is the image of the étale object the generating section has been
restricted to. -/
theorem exists_sieve_imageOpen_section (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u))
    {V : SmallEtale B S hS} (x : ((toposInverseImage B S hS).obj F).obj.obj (op V)) :
    ∃ T : Sieve V, T ∈ topology B S hS V ∧ ∀ ⦃W : SmallEtale B S hS⦄ (g : W ⟶ V), T g →
      ∃ y : F.obj.obj (op (imageOpen B S hS W)),
        (imageOpenToInverseImageComp B S hS F).app (op W) y =
          ((toposInverseImage B S hS).obj F).obj.map g.op x :=
  ⟨Presheaf.imageSieve (imageOpenToInverseImageComp B S hS F) x,
    Presheaf.imageSieve_mem (topology B S hS) (imageOpenToInverseImageComp B S hS F) x,
    fun _ _ hg => hg⟩

end AlgebraicGeometry.SmallEtale

end
