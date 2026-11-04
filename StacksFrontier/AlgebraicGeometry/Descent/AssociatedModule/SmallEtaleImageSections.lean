module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# `ε⁻¹𝒪_{S_Zar}` as the étale sheafification of `(f : V → S) ↦ 𝒪_S(f(V))`

Let `ε = id_{small, étale, Zar} : S_étale → S_Zar` be the morphism of ringed sites of
Stacks 070R, carried by the inclusion `AlgebraicGeometry.SmallEtale.opensToSmallEtale` of the
small Zariski site of `S` into the small étale site of `S`.  This module identifies the inverse
image `ε⁻¹𝒪_{S_Zar}` of the structure sheaf: an étale morphism is open, so the image `f(V)` of
an object `f : V → S` of the small étale site is an open of `S`, and `ε⁻¹𝒪_{S_Zar}` is the
étale sheafification of the presheaf of commutative rings `(f : V → S) ↦ 𝒪_S(f(V))`.

The mechanism is an *adjunction*, not a colimit computation.  Taking the image open is a functor
`S_étale ⥤ S_Zar` left adjoint to the inclusion (`imageOpenAdjunction`): a morphism from `V` to
an open `U` exists exactly when `f(V) ⊆ U`, and is then unique.  Precomposition with the
opposite of a left adjoint is itself left adjoint to precomposition with the opposite of the
right adjoint, so `P ↦ (image open)ᵒᵖ ⋙ P` is a left Kan extension along `(opensToSmallEtale)ᵒᵖ`
on the nose, and composing it with sheafification produces a left adjoint of the pushforward of
sheaves of commutative rings.  The inverse image functor being *defined* as a chosen left adjoint
of that pushforward, uniqueness of left adjoints identifies it with the sheafification of
`(f : V → S) ↦ 𝒪_S(f(V))`, and the comparison map is the sheafification unit, hence locally
bijective.

Over this presheaf of rings, the global functions `V ↦ Γ(V, 𝒪_V)` of the small étale site form
a presheaf of modules, by restricting scalars along the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.
That restriction is the transpose of the structure-sheaf comparison
`AlgebraicGeometry.SmallEtale.commRingStructureMap` of `ε` under the same adjunction.

## Main definitions

* `AlgebraicGeometry.SmallEtale.imageOpen`: the image of an object of the small étale site of
  `S`, an open of `S` because an étale morphism is open.
* `AlgebraicGeometry.SmallEtale.imageOpenFunctor`: that image as a functor `S_étale ⥤ S_Zar`.
* `AlgebraicGeometry.SmallEtale.imageSectionsPresheaf`: the presheaf of commutative rings
  `(f : V → S) ↦ 𝒪_S(f(V))` on the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.inverseImageCommRing`: `ε⁻¹` on sheaves of commutative rings.
* `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage`: the comparison map from
  `(f : V → S) ↦ 𝒪_S(f(V))` to `ε⁻¹𝒪_{S_Zar}`, and
  `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImageRing`, the same map read on sheaves
  of not necessarily commutative rings.
* `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`: the structure map
  `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}`, whose flatness is Stacks 0GNA.
* `AlgebraicGeometry.SmallEtale.imageSectionsRestriction`: the restriction
  `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.
* `AlgebraicGeometry.SmallEtale.sectionsAsImageSectionsModule`: the global functions of the small
  étale site as a presheaf of modules over `(f : V → S) ↦ 𝒪_S(f(V))`.

## Main results

* `AlgebraicGeometry.SmallEtale.imageOpenAdjunction`: the image open is left adjoint to the
  inclusion of the small Zariski site of `S` into the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.isLocallyInjective_imageSectionsToInverseImage` and
  `AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImage`: the comparison
  map is locally bijective, i.e. `ε⁻¹𝒪_{S_Zar}` is the étale sheafification of
  `(f : V → S) ↦ 𝒪_S(f(V))`.  Their `RingCat`-valued companions are
  `AlgebraicGeometry.SmallEtale.isLocallyInjective_imageSectionsToInverseImageRing` and
  `AlgebraicGeometry.SmallEtale.isLocallySurjective_imageSectionsToInverseImageRing`.
* `AlgebraicGeometry.SmallEtale.homEquiv_imageSectionsRestriction`: the restriction
  `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is adjoint to the structure-sheaf comparison of `ε`.
* `AlgebraicGeometry.SmallEtale.imageSectionsToInverseImage_comp_inverseImageStructureMap`: the
  comparison map followed by the structure map `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}` is that
  restriction.

## Implementation notes

The inverse image of sheaves of commutative rings is `CategoryTheory.Functor.sheafPullback`,
Mathlib's universe-general pullback of sheaves along a continuous functor.  The bundled
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is unavailable: it requires the two ringed
topoi to share all three universes, and the small Zariski site of `S` has its objects one
universe below those of the small étale site.  The right adjoint it is a left adjoint of is
exhibited as such by `inverseImageAuxAdjunction` here, so no left Kan extension has to be
assumed to exist.

Two spellings of the sheafification of `(f : V → S) ↦ 𝒪_S(f(V))` occur, and the comparison map
is a composite of maps between them; `inverseImageIso` names the comparison isomorphism with its
source written as `CategoryTheory.sheafify`, which is the spelling in which the instances for
`CategoryTheory.toSheafify` are stated, so that local bijectivity of the composite is found by
instance search.

## References

* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a scheme `S`, as a sheaf of commutative rings on the small Zariski
site of `S`.  This is the structure sheaf of `AlgebraicGeometry.Scheme.zariskiRingedTopos`, named
separately so that its type is recorded as a sheaf for `Opens.grothendieckTopology ↥S`. -/
public noncomputable def Scheme.zariskiCommRingSheaf (S : Scheme.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u} :=
  S.sheaf

/-- The underlying presheaf of `S.zariskiCommRingSheaf` is the structure presheaf of `S`. -/
@[simp]
public theorem Scheme.zariskiCommRingSheaf_obj (S : Scheme.{u}) :
    S.zariskiCommRingSheaf.obj = S.presheaf := rfl

/-- The structure sheaf of `S.zariskiRingedTopos` is `S.zariskiCommRingSheaf`. -/
@[simp]
public theorem Scheme.zariskiRingedTopos_O_eq (S : Scheme.{u}) :
    S.zariskiRingedTopos.O = S.zariskiCommRingSheaf := rfl

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The image of an object of the small étale site -/

/-- There is at most one morphism from an object of the small étale site of `S` into an open of
`S`, the open immersion of that open being a monomorphism. -/
public theorem hom_opensToSmallEtale_ext {V : SmallEtale B S hS} {U : S.Opens}
    (f g : V ⟶ (opensToSmallEtale B S hS).obj U) : f = g :=
  Subsingleton.elim f g

/-- **The structure morphism of an object of the small étale site of `S` is universally open**
(Stacks 03WT), being étale. -/
public instance universallyOpen_structureMorphism (V : SmallEtale B S hS) :
    UniversallyOpen V.obj.hom.hom :=
  inferInstanceAs (UniversallyOpen (B.inclusion.map V.obj.hom))

/-- **The image of an object of the small étale site of `S` is an open of `S`** (Stacks 03WT):
the structure morphism of an object of the small étale site is étale, hence open. -/
public def imageOpen (V : SmallEtale B S hS) : S.Opens :=
  ⟨Set.range ⇑V.obj.hom.hom, (Scheme.Hom.isOpenMap V.obj.hom.hom).isOpen_range⟩

/-- The underlying set of the image open of `V` is the range of the structure morphism of `V`. -/
@[simp]
public theorem imageOpen_coe (V : SmallEtale B S hS) :
    (imageOpen B S hS V : Set S) = Set.range ⇑V.obj.hom.hom := rfl

/-- The image of an object of the small étale site of `S` is contained in an open `U` exactly
when the structure morphism has range inside `U`. -/
public theorem imageOpen_le_iff {V : SmallEtale B S hS} {U : S.Opens} :
    imageOpen B S hS V ≤ U ↔ Set.range ⇑V.obj.hom.hom ⊆ (U : Set S) := Iff.rfl

/-- The image of an open of `S`, viewed in the small étale site, is that open. -/
@[simp]
public theorem imageOpen_opensObj (U : S.Opens) :
    imageOpen B S hS (opensObj B S hS U) = U :=
  TopologicalSpace.Opens.ext (by
    show Set.range ⇑(BigEtaleOver.opensObj B S hS U).hom.hom = _
    rw [BigEtaleOver.opensObj_hom_hom, Scheme.Opens.range_ι])

/-- A morphism of the small étale site of `S` is compatible with the structure morphisms, so it
shrinks images. -/
public theorem imageOpen_le_imageOpen {V W : SmallEtale B S hS} (g : V ⟶ W) :
    imageOpen B S hS V ≤ imageOpen B S hS W := by
  have h : V.obj.hom.hom = g.hom.left.hom ≫ W.obj.hom.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun k : V.obj.left ⟶ B.obj S hS => k.hom) (Over.w g.hom).symm
  rintro x ⟨y, rfl⟩
  exact ⟨g.hom.left.hom y, by rw [h]; simp⟩

/-- **The image open as a functor `S_étale ⥤ S_Zar`.** -/
public def imageOpenFunctor : SmallEtale B S hS ⥤ S.Opens where
  obj V := imageOpen B S hS V
  map g := homOfLE (imageOpen_le_imageOpen B S hS g)

/-- `imageOpenFunctor` sends an object of the small étale site of `S` to its image open. -/
@[simp]
public theorem imageOpenFunctor_obj (V : SmallEtale B S hS) :
    (imageOpenFunctor B S hS).obj V = imageOpen B S hS V := rfl

/-- The canonical factorization of an object of the small étale site of `S` through its image
open. -/
public noncomputable def toImageOpen (V : SmallEtale B S hS) :
    V ⟶ (opensToSmallEtale B S hS).obj (imageOpen B S hS V) :=
  homOfRangeLe B S hS _ (le_refl _)

/-- **The image open is left adjoint to the inclusion of the small Zariski site of `S` into the
small étale site of `S`:** a morphism from `V` to an open `U` of `S` exists exactly when the
image of `V` is contained in `U`, and it is then unique.

This is the openness of étale morphisms (Stacks 03WT) in the form the inverse image `ε⁻¹` of
`AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom` consumes. -/
public noncomputable def imageOpenAdjunction :
    imageOpenFunctor B S hS ⊣ opensToSmallEtale B S hS where
  unit := { app := fun V => toImageOpen B S hS V
            naturality := fun _ _ _ => hom_opensToSmallEtale_ext B S hS _ _ }
  counit := { app := fun U => homOfLE (imageOpen_opensObj B S hS U).le
              naturality := fun _ _ _ => Subsingleton.elim _ _ }
  left_triangle_components _ := Subsingleton.elim _ _
  right_triangle_components _ := hom_opensToSmallEtale_ext B S hS _ _

/-! ### The presheaf of sections over the image open -/

/-- **The presheaf of commutative rings `(f : V → S) ↦ 𝒪_S(f(V))` on the small étale site of
`S`**: the sections of the structure sheaf of `S` over the image open of `V`. -/
public def imageSectionsPresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (imageOpenFunctor B S hS).op ⋙ S.presheaf

/-- The value of `imageSectionsPresheaf` at `V` is the ring of sections of the structure sheaf
of `S` over the image open of `V`. -/
@[simp]
public theorem imageSectionsPresheaf_obj (V : (SmallEtale B S hS)ᵒᵖ) :
    (imageSectionsPresheaf B S hS).obj V
      = S.presheaf.obj (Opposite.op (imageOpen B S hS V.unop)) := rfl

/-! ### Sheafification on the small étale site at `CommRingCat` -/

/-- Presheaves of commutative rings on the small étale site of `S` have a sheafification, the
site being essentially small. -/
public instance hasSheafify_commRing : HasSheafify (topology B S hS) CommRingCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of presheaves of commutative rings on the small étale site of `S` are the
locally bijective maps, the site being essentially small. -/
public instance wEqualsLocallyBijective_commRing :
    (topology B S hS).WEqualsLocallyBijective CommRingCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-! ### `ε⁻¹` of a sheaf of commutative rings -/

/-- Sheafification of `(f : V → S) ↦ 𝒪_S(f(V))`, as a functor of the sheaf of commutative rings
on the small Zariski site of `S` whose sections over the image opens are taken.

This is the model of `ε⁻¹` built from the adjunction of `imageOpenAdjunction`; it is identified
with `inverseImageCommRing` by `inverseImageAuxIso`. -/
public noncomputable def inverseImageAux :
    Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u} ⥤
      Sheaf (topology B S hS) CommRingCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u} ⋙
    (whiskeringLeft _ _ _).obj (imageOpenFunctor B S hS).op ⋙
      presheafToSheaf (topology B S hS) CommRingCat.{u}

/-- **Sheafifying `(f : V → S) ↦ 𝒪_S(f(V))` is left adjoint to the pushforward of sheaves of
commutative rings along the inclusion of the small Zariski site of `S`.**

Precomposition with `(imageOpenFunctor)ᵒᵖ` is left adjoint to precomposition with
`(opensToSmallEtale)ᵒᵖ` because the two functors are adjoint, and sheafification is left adjoint
to the inclusion of sheaves; the composite of the two adjunctions restricts to sheaves on the
Zariski side because the inclusion of sheaves is fully faithful. -/
public noncomputable def inverseImageAuxAdjunction :
    inverseImageAux B S hS ⊣
      (opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  ((Adjunction.whiskerLeft CommRingCat.{u} (imageOpenAdjunction B S hS).op).comp
      (sheafificationAdjunction (topology B S hS) CommRingCat.{u})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (FullyFaithful.id _)
    (Iso.refl (sheafToPresheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u} ⋙
      ((whiskeringLeft _ _ _).obj (imageOpenFunctor B S hS).op ⋙
        presheafToSheaf (topology B S hS) CommRingCat.{u})))
    (Iso.refl _)

/-- The pushforward of sheaves of commutative rings along the inclusion of the small Zariski
site of `S` into the small étale site has a left adjoint, namely `inverseImageAux`. -/
public instance isRightAdjoint_sheafPushforwardContinuous :
    ((opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS)).IsRightAdjoint :=
  (inverseImageAuxAdjunction B S hS).isRightAdjoint

/-- **`ε⁻¹` on sheaves of commutative rings**, for `ε = id_{small, étale, Zar}` the morphism of
ringed sites `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`: the pullback of sheaves
along the continuous inclusion of the small Zariski site of `S` into the small étale site. -/
public noncomputable def inverseImageCommRing :
    Sheaf (Opens.grothendieckTopology ↥S) CommRingCat.{u} ⥤
      Sheaf (topology B S hS) CommRingCat.{u} :=
  (opensToSmallEtale B S hS).sheafPullback CommRingCat.{u}
    (Opens.grothendieckTopology ↥S) (topology B S hS)

/-- `ε⁻¹` is left adjoint to `ε_*` on sheaves of commutative rings. -/
public noncomputable def inverseImageCommRingAdjunction :
    inverseImageCommRing B S hS ⊣
      (opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  Functor.sheafAdjunctionContinuous _ _ _ _

/-- **`ε⁻¹` is sheafification of the sections over the image opens.**  Both are left adjoint to
the pushforward of sheaves of commutative rings along the inclusion of the small Zariski site of
`S`, and a left adjoint is unique up to canonical isomorphism. -/
public noncomputable def inverseImageAuxIso :
    inverseImageAux B S hS ≅ inverseImageCommRing B S hS :=
  Adjunction.leftAdjointUniq (inverseImageAuxAdjunction B S hS)
    (inverseImageCommRingAdjunction B S hS)

/-- `inverseImageAuxIso` at the structure sheaf of `S`, read on underlying presheaves: the
sheafification of `(f : V → S) ↦ 𝒪_S(f(V))` is `ε⁻¹𝒪_{S_Zar}`. -/
public noncomputable def inverseImageIso :
    sheafify (topology B S hS) (imageSectionsPresheaf B S hS) ⟶
      ((inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf).obj :=
  ((inverseImageAuxIso B S hS).app S.zariskiCommRingSheaf).hom.hom

/-- `inverseImageIso` is an isomorphism, being the underlying morphism of presheaves of an
isomorphism of sheaves. -/
public instance isIso_inverseImageIso : IsIso (inverseImageIso B S hS) :=
  inferInstanceAs (IsIso ((sheafToPresheaf (topology B S hS) CommRingCat.{u}).mapIso
    ((inverseImageAuxIso B S hS).app S.zariskiCommRingSheaf)).hom)

/-- **The comparison map `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}`**: the sheafification
unit, followed by the identification of the sheafification with `ε⁻¹𝒪_{S_Zar}`.

Stacks' proof of 0GNA runs through this map: it exhibits `ε⁻¹𝒪_{S_Zar}` as the étale
sheafification of the sections of `𝒪_S` over the image opens. -/
public noncomputable def imageSectionsToInverseImage :
    imageSectionsPresheaf B S hS ⟶
      ((inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf).obj :=
  toSheafify (topology B S hS) (imageSectionsPresheaf B S hS) ≫ inverseImageIso B S hS

/-- **`ε⁻¹𝒪_{S_Zar}` is a sheafification of `(f : V → S) ↦ 𝒪_S(f(V))`, injective half:** the
comparison map is locally injective, being a sheafification unit composed with an
isomorphism. -/
public instance isLocallyInjective_imageSectionsToInverseImage :
    Presheaf.IsLocallyInjective (topology B S hS) (imageSectionsToInverseImage B S hS) :=
  inferInstanceAs (Presheaf.IsLocallyInjective (topology B S hS)
    (toSheafify (topology B S hS) (imageSectionsPresheaf B S hS) ≫ inverseImageIso B S hS))

/-- **`ε⁻¹𝒪_{S_Zar}` is a sheafification of `(f : V → S) ↦ 𝒪_S(f(V))`, surjective half:** the
comparison map is locally surjective, being a sheafification unit composed with an
isomorphism. -/
public instance isLocallySurjective_imageSectionsToInverseImage :
    Presheaf.IsLocallySurjective (topology B S hS) (imageSectionsToInverseImage B S hS) :=
  inferInstanceAs (Presheaf.IsLocallySurjective (topology B S hS)
    (toSheafify (topology B S hS) (imageSectionsPresheaf B S hS) ≫ inverseImageIso B S hS))

/-- The comparison map `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}` read on presheaves of not
necessarily commutative rings, the form in which Stacks 0GN1 takes it. -/
public noncomputable def imageSectionsToInverseImageRing :
    imageSectionsPresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      ((sheafCompose (topology B S hS) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf)).obj :=
  whiskerRight (imageSectionsToInverseImage B S hS) (forget₂ CommRingCat.{u} RingCat.{u})

/-- `isLocallyInjective_imageSectionsToInverseImage`, read on presheaves of not necessarily
commutative rings: local injectivity depends only on the underlying presheaves of sets. -/
public instance isLocallyInjective_imageSectionsToInverseImageRing :
    Presheaf.IsLocallyInjective (topology B S hS)
      (imageSectionsToInverseImageRing B S hS) := by
  rw [← Presheaf.isLocallyInjective_forget_iff]
  exact inferInstanceAs (Presheaf.IsLocallyInjective (topology B S hS)
    (whiskerRight (imageSectionsToInverseImage B S hS) (forget CommRingCat.{u})))

/-- `isLocallySurjective_imageSectionsToInverseImage`, read on presheaves of not necessarily
commutative rings: local surjectivity depends only on the underlying presheaves of sets. -/
public instance isLocallySurjective_imageSectionsToInverseImageRing :
    Presheaf.IsLocallySurjective (topology B S hS)
      (imageSectionsToInverseImageRing B S hS) := by
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact inferInstanceAs (Presheaf.IsLocallySurjective (topology B S hS)
    (whiskerRight (imageSectionsToInverseImage B S hS) (forget CommRingCat.{u})))

/-! ### The structure map of `ε` after taking the inverse image -/

/-- **The structure map `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}`** of the morphism of ringed sites
`ε = id_{small, étale, Zar}`: the transpose of
`AlgebraicGeometry.SmallEtale.commRingStructureMap` under the adjunction between `ε⁻¹` and the
pushforward of sheaves of commutative rings.  Stacks 0GNA asserts that this morphism of sheaves
of commutative rings is flat. -/
public noncomputable def inverseImageStructureMap :
    (inverseImageCommRing B S hS).obj S.zariskiCommRingSheaf ⟶ (commRingStructureSheaf B S hS) :=
  ((inverseImageCommRingAdjunction B S hS).homEquiv _ _).symm (commRingStructureMap B S hS)

/-- The structure map `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}` read on the sheafification model
`inverseImageAux` of `ε⁻¹`. -/
public noncomputable def inverseImageAuxStructureMap :
    (inverseImageAux B S hS).obj S.zariskiCommRingSheaf ⟶ (commRingStructureSheaf B S hS) :=
  ((inverseImageAuxAdjunction B S hS).homEquiv _ _).symm (commRingStructureMap B S hS)

/-- The identification of the sheafification of `(f : V → S) ↦ 𝒪_S(f(V))` with `ε⁻¹𝒪_{S_Zar}`
carries one structure map to the other, both being transposes of the same structure-sheaf
comparison. -/
public theorem inverseImageAuxIso_hom_app_comp_inverseImageStructureMap :
    ((inverseImageAuxIso B S hS).app S.zariskiCommRingSheaf).hom ≫
        inverseImageStructureMap B S hS
      = inverseImageAuxStructureMap B S hS := by
  refine (Adjunction.homEquiv_apply_eq _ _ _).1 ?_
  simp only [inverseImageStructureMap, inverseImageAuxIso, Adjunction.homEquiv_unit,
    Functor.map_comp, Iso.app_hom, Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  rw [← Adjunction.homEquiv_unit]
  exact Equiv.apply_symm_apply _ _

/-! ### The global functions as a module over the sections over the image opens -/

/-- **The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`**: the transpose of the structure-sheaf comparison
of `ε` under the adjunction between the image open and the inclusion of the small Zariski site
of `S`.  Over `V` it restricts a function on the image open of `V` along the canonical
factorization of `V` through that open. -/
public noncomputable def imageSectionsRestriction :
    imageSectionsPresheaf B S hS ⟶ (commRingStructureSheaf B S hS).obj :=
  ((Adjunction.whiskerLeft CommRingCat.{u} (imageOpenAdjunction B S hS).op).homEquiv
    S.zariskiCommRingSheaf.obj (commRingStructureSheaf B S hS).obj).symm
      (commRingStructureMap B S hS).hom

/-- Over `V`, `imageSectionsRestriction` is the structure-sheaf comparison of `ε` at the image
open of `V`, followed by restriction along the factorization `toImageOpen` of `V` through that
open. -/
@[simp]
public theorem imageSectionsRestriction_app (V : (SmallEtale B S hS)ᵒᵖ) :
    (imageSectionsRestriction B S hS).app V
      = (commRingStructureMap B S hS).hom.app
            (Opposite.op (imageOpen B S hS V.unop)) ≫
          (commRingStructureSheaf B S hS).obj.map (toImageOpen B S hS V.unop).op :=
  rfl

/-- **The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is adjoint to the structure-sheaf comparison of
`ε`.**  Transposing it back along the adjunction between the image open and the inclusion of the
small Zariski site of `S` returns `AlgebraicGeometry.SmallEtale.commRingStructureMap`, so over
an open of `S` the restriction is the identification of the sections of `𝒪_S` over that open
with the functions on it. -/
public theorem homEquiv_imageSectionsRestriction :
    (Adjunction.whiskerLeft CommRingCat.{u} (imageOpenAdjunction B S hS).op).homEquiv
        S.zariskiCommRingSheaf.obj (commRingStructureSheaf B S hS).obj
        (imageSectionsRestriction B S hS)
      = (commRingStructureMap B S hS).hom :=
  Equiv.apply_symm_apply _ _

/-- **The sheafification unit composed with the structure map is the restriction
`𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.**  Both are transposes of
`AlgebraicGeometry.SmallEtale.commRingStructureMap`: the left-hand side under the composite of
the sheafification adjunction with the adjunction between the image open and the inclusion of
the small Zariski site of `S`, the right-hand side under the second alone. -/
public theorem toSheafify_comp_inverseImageAuxStructureMap :
    toSheafify (topology B S hS) (imageSectionsPresheaf B S hS) ≫
        (inverseImageAuxStructureMap B S hS).hom
      = imageSectionsRestriction B S hS := by
  refine (Adjunction.homEquiv_apply_eq
    (Adjunction.whiskerLeft CommRingCat.{u} (imageOpenAdjunction B S hS).op) _ _).1 ?_
  have h0 : (inverseImageAuxAdjunction B S hS).homEquiv
      S.zariskiCommRingSheaf (commRingStructureSheaf B S hS)
      (inverseImageAuxStructureMap B S hS) = commRingStructureMap B S hS :=
    Equiv.apply_symm_apply _ _
  have h := congrArg (fun f => f.hom) h0
  simp only [Adjunction.homEquiv_unit] at h ⊢
  rw [← h]
  simp only [inverseImageAuxStructureMap, inverseImageAuxAdjunction]
  rfl

/-- **The comparison map `(f : V → S) ↦ 𝒪_S(f(V))` `⟶` `ε⁻¹𝒪_{S_Zar}`, followed by the structure
map `ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}`, is the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.**

This is what makes the presheaf of modules
`AlgebraicGeometry.SmallEtale.sectionsAsImageSectionsModule` the right input for Stacks 0GN1:
the module structure it carries over `(f : V → S) ↦ 𝒪_S(f(V))` is the one induced by the
structure map of `ε` whose flatness Stacks 0GNA asserts. -/
public theorem imageSectionsToInverseImage_comp_inverseImageStructureMap :
    imageSectionsToInverseImage B S hS ≫ (inverseImageStructureMap B S hS).hom
      = imageSectionsRestriction B S hS := by
  have h : inverseImageIso B S hS ≫ (inverseImageStructureMap B S hS).hom
      = (inverseImageAuxStructureMap B S hS).hom :=
    congrArg (fun f => f.hom)
      (inverseImageAuxIso_hom_app_comp_inverseImageStructureMap B S hS)
  rw [imageSectionsToInverseImage, Category.assoc, h]
  exact toSheafify_comp_inverseImageAuxStructureMap B S hS

/-- The restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`, read on presheaves of not necessarily commutative
rings: this is the morphism of presheaves of rings along which the global functions of the small
étale site are a presheaf of modules over `(f : V → S) ↦ 𝒪_S(f(V))`. -/
public noncomputable def imageSectionsRestrictionRing :
    imageSectionsPresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (structureSheaf B S hS).obj :=
  whiskerRight (imageSectionsRestriction B S hS) (forget₂ CommRingCat.{u} RingCat.{u})

/-- **The global functions `V ↦ Γ(V, 𝒪_V)` of the small étale site of `S` as a presheaf of
modules over `(f : V → S) ↦ 𝒪_S(f(V))`**, the module structure being restriction of scalars
along `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)`.

Its sheafification over the comparison map `imageSectionsToInverseImage` is the object whose
flatness Stacks 0GNA asserts. -/
public noncomputable def sectionsAsImageSectionsModule :
    PresheafOfModules.{u}
      (imageSectionsPresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (PresheafOfModules.restrictScalars (imageSectionsRestrictionRing B S hS)).obj
    (PresheafOfModules.unit (structureSheaf B S hS).obj)

/-- The presheaf of abelian groups underlying the presheaf of modules
`sectionsAsImageSectionsModule` is the global functions `V ↦ Γ(V, 𝒪_V)` of the small étale site
of `S`: restricting scalars does not change the underlying additive group. -/
public theorem toPresheaf_obj_sectionsAsImageSectionsModule :
    (PresheafOfModules.toPresheaf
          (imageSectionsPresheaf B S hS ⋙ forget₂ CommRingCat.{u} RingCat.{u})).obj
        (sectionsAsImageSectionsModule B S hS)
      = (PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).obj
          (PresheafOfModules.unit (structureSheaf B S hS).obj) :=
  rfl

end SmallEtale

end AlgebraicGeometry

end
