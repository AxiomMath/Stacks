module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections

/-!
# `ε⁻¹` of an arbitrary sheaf of commutative rings as a sheafification of sections over images

Let `S` be a scheme in a big étale site `B` and let
`ε = id_{small, étale, Zar} : S_étale ⟶ S_Zar` be the morphism of ringed sites of Stacks 070R.
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleImageSections.lean` exhibits
`ε⁻¹𝒪_{S_Zar}` as the étale sheafification of the presheaf `(h : V → S) ↦ 𝒪_S(h(V))`, which is
the route Stacks' proof of 0GNA takes.  Nothing in that argument is about the structure sheaf:
`AlgebraicGeometry.SmallEtale.inverseImageAux` and
`AlgebraicGeometry.SmallEtale.inverseImageAuxIso` are already stated for an arbitrary sheaf of
commutative rings on the small Zariski site of `S`, and only the comparison map itself was
specialized.  This module states it in that generality, and adds its naturality in the
coefficient sheaf.

The coefficient sheaf this is wanted for is `f⁻¹𝒪_Y` for a morphism `f : S ⟶ Y` of schemes:
the vanishing of a derivation of `𝒪_{S_étale}` over `ε⁻¹f⁻¹𝒪_Y` is checked through this
local surjectivity, exactly as the vanishing over `ε⁻¹𝒪_{S_Zar}` is.

## Main definitions

* `AlgebraicGeometry.SmallEtale.imageSectionsPresheafOf` is `(h : V → S) ↦ 𝒢(h(V))` for a sheaf
  of commutative rings `𝒢` on the small Zariski site of `S`, with
  `AlgebraicGeometry.SmallEtale.imageSectionsPresheafMapOf` its functoriality in `𝒢`.
* `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageOf` is the comparison map
  `(h : V → S) ↦ 𝒢(h(V))` `⟶` `ε⁻¹𝒢`, the sheafification unit followed by the identification
  `AlgebraicGeometry.SmallEtale.inverseImageIsoOf` of the sheafification with `ε⁻¹𝒢`.

## Main results

* `AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImageOf`: the
  comparison map is locally surjective, so a section of `ε⁻¹𝒢` is étale-locally a section of
  `𝒢` over an image open.  This is the statement a vanishing argument over `ε⁻¹𝒢` runs on.
* `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageOf_naturality` and
  `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageOf_app_apply_naturality`: the
  comparison map is natural in the coefficient sheaf, as a morphism of presheaves and on
  sections.  This is what carries a section of `ε⁻¹f⁻¹𝒪_Y` into `ε⁻¹𝒪_{S_Zar}` along a map
  whose effect on image sections is the structure map of `f` over the image open.

## Implementation notes

The specialization at `𝒢 = 𝒪_{S_Zar}` of everything here is definitionally the existing
structure-sheaf version:
`AlgebraicGeometry.SmallEtale.imageSectionsPresheafOf_zariskiCommRingSheaf` and
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageOf_zariskiCommRingSheaf` record that by
`rfl`.  So the structure-sheaf map `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage` is not
restated, and lemmas proved about it — in particular
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage_comp_inverseImageStructureMap`, which
identifies its composite with the structure map of `ε` — apply to the general map at that
coefficient sheaf without transport.

## References

* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presheaf of commutative rings `(h : V → S) ↦ 𝒢(h(V))` on the small étale site of
`S`**, for `𝒢` a sheaf of commutative rings on the small Zariski site of `S`: the sections of
`𝒢` over the image open of `V`.  At `𝒢 = 𝒪_{S_Zar}` this is
`AlgebraicGeometry.SmallEtale.imageSectionsPresheaf`. -/
public def imageSectionsPresheafOf (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (imageOpenFunctor B S hS).op ⋙ G.obj

/-- The value of `AlgebraicGeometry.SmallEtale.imageSectionsPresheafOf` at `V` is the ring of
sections of `𝒢` over the image open of `V`. -/
@[simp]
public theorem imageSectionsPresheafOf_obj
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) (V : (SmallEtale B S hS)ᵒᵖ) :
    (imageSectionsPresheafOf B S hS G).obj V
      = G.obj.obj (Opposite.op (imageOpen B S hS V.unop)) := rfl

/-- At the structure sheaf the general image-sections presheaf is `imageSectionsPresheaf`. -/
public theorem imageSectionsPresheafOf_zariskiCommRingSheaf :
    imageSectionsPresheafOf B S hS S.zariskiCommRingSheaf = imageSectionsPresheaf B S hS := rfl

/-- The functoriality of `(h : V → S) ↦ 𝒢(h(V))` in the coefficient sheaf `𝒢`. -/
public def imageSectionsPresheafMapOf
    {G G' : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}} (α : G ⟶ G') :
    imageSectionsPresheafOf B S hS G ⟶ imageSectionsPresheafOf B S hS G' :=
  whiskerLeft (imageOpenFunctor B S hS).op α.hom

/-- The component of `AlgebraicGeometry.SmallEtale.imageSectionsPresheafMapOf α` at `V` is the
component of `α` at the image open of `V`. -/
@[simp]
public theorem imageSectionsPresheafMapOf_app
    {G G' : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}} (α : G ⟶ G')
    (V : (SmallEtale B S hS)ᵒᵖ) :
    (imageSectionsPresheafMapOf B S hS α).app V
      = α.hom.app (Opposite.op (imageOpen B S hS V.unop)) := rfl

/-- **`ε⁻¹𝒢` is a sheafification of `(h : V → S) ↦ 𝒢(h(V))`.**  This is
`AlgebraicGeometry.SmallEtale.inverseImageAuxIso` at `𝒢`, read on underlying presheaves; at
`𝒢 = 𝒪_{S_Zar}` it is `AlgebraicGeometry.SmallEtale.inverseImageIso`. -/
public noncomputable def inverseImageIsoOf
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    sheafify (topology B S hS) (imageSectionsPresheafOf B S hS G) ⟶
      ((inverseImageCommRing B S hS).obj G).obj :=
  ((inverseImageAuxIso B S hS).app G).hom.hom

/-- `AlgebraicGeometry.SmallEtale.inverseImageIsoOf` is an isomorphism. -/
public instance isIso_inverseImageIsoOf
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    IsIso (inverseImageIsoOf B S hS G) :=
  inferInstanceAs (IsIso ((sheafToPresheaf (topology B S hS) CommRingCat.{u}).mapIso
    ((inverseImageAuxIso B S hS).app G)).hom)

/-- **The comparison map `(h : V → S) ↦ 𝒢(h(V))` `⟶` `ε⁻¹𝒢`**: the sheafification unit,
followed by the identification of the sheafification with `ε⁻¹𝒢`.  At `𝒢 = 𝒪_{S_Zar}` this is
`AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage`. -/
public noncomputable def imageSectionsToInverseImageOf
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    imageSectionsPresheafOf B S hS G ⟶ ((inverseImageCommRing B S hS).obj G).obj :=
  toSheafify (topology B S hS) (imageSectionsPresheafOf B S hS G) ≫ inverseImageIsoOf B S hS G

/-- At the structure sheaf the general comparison map is `imageSectionsToInverseImage`. -/
public theorem imageSectionsToInverseImageOf_zariskiCommRingSheaf :
    imageSectionsToInverseImageOf B S hS S.zariskiCommRingSheaf
      = imageSectionsToInverseImage B S hS := rfl

/-- **`ε⁻¹𝒢` is a sheafification of `(h : V → S) ↦ 𝒢(h(V))`, injective half:** the comparison
map is locally injective, being a sheafification unit composed with an isomorphism. -/
public instance isLocallyInjective_imageSectionsToInverseImageOf
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    Presheaf.IsLocallyInjective (topology B S hS) (imageSectionsToInverseImageOf B S hS G) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (topology B S hS)
    (toSheafify (topology B S hS) (imageSectionsPresheafOf B S hS G) ≫
      inverseImageIsoOf B S hS G))

/-- **`ε⁻¹𝒢` is a sheafification of `(h : V → S) ↦ 𝒢(h(V))`, surjective half:** the comparison
map is locally surjective, being a sheafification unit composed with an isomorphism.  So a
section of `ε⁻¹𝒢` over an object of the small étale site is, on an étale covering of that
object, a section of `𝒢` over an image open. -/
public instance isLocallySurjective_imageSectionsToInverseImageOf
    (G : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}) :
    Presheaf.IsLocallySurjective (topology B S hS) (imageSectionsToInverseImageOf B S hS G) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (topology B S hS)
    (toSheafify (topology B S hS) (imageSectionsPresheafOf B S hS G) ≫
      inverseImageIsoOf B S hS G))

/-- The identification of the sheafification of `(h : V → S) ↦ 𝒢(h(V))` with `ε⁻¹𝒢` is natural
in `𝒢`, `AlgebraicGeometry.SmallEtale.inverseImageAuxIso` being an isomorphism of functors. -/
public theorem sheafifyMap_comp_inverseImageIsoOf
    {G G' : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}} (α : G ⟶ G') :
    sheafifyMap (topology B S hS) (imageSectionsPresheafMapOf B S hS α) ≫
        inverseImageIsoOf B S hS G'
      = inverseImageIsoOf B S hS G ≫ ((inverseImageCommRing B S hS).map α).hom :=
  congrArg (fun m : (inverseImageAux B S hS).obj G ⟶ (inverseImageCommRing B S hS).obj G' =>
    m.hom) ((inverseImageAuxIso B S hS).hom.naturality α)

/-- **The comparison map is natural in the coefficient sheaf.**  Both the sheafification unit
and the identification of the sheafification with `ε⁻¹` are natural, the latter because
`AlgebraicGeometry.SmallEtale.inverseImageAuxIso` is an isomorphism of functors. -/
public theorem imageSectionsToInverseImageOf_naturality
    {G G' : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}} (α : G ⟶ G') :
    imageSectionsPresheafMapOf B S hS α ≫ imageSectionsToInverseImageOf B S hS G'
      = imageSectionsToInverseImageOf B S hS G ≫
          ((inverseImageCommRing B S hS).map α).hom := by
  rw [imageSectionsToInverseImageOf, imageSectionsToInverseImageOf, ← Category.assoc,
    toSheafify_naturality, Category.assoc, sheafifyMap_comp_inverseImageIsoOf,
    ← Category.assoc]

/-- The naturality of the comparison map in the coefficient sheaf, read on a section. -/
public theorem imageSectionsToInverseImageOf_app_apply_naturality
    {G G' : Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u}} (α : G ⟶ G')
    (V : (SmallEtale B S hS)ᵒᵖ) (s : (imageSectionsPresheafOf B S hS G).obj V) :
    ((imageSectionsToInverseImageOf B S hS G').app V).hom
        ((α.hom.app (Opposite.op (imageOpen B S hS V.unop))).hom s)
      = (((inverseImageCommRing B S hS).map α).hom.app V).hom
          (((imageSectionsToInverseImageOf B S hS G).app V).hom s) :=
  congrArg (fun m : imageSectionsPresheafOf B S hS G ⟶
      ((inverseImageCommRing B S hS).obj G').obj => (m.app V).hom s)
    (imageSectionsToInverseImageOf_naturality B S hS α)

end AlgebraicGeometry.SmallEtale

end
