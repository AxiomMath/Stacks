module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ε = id_{small, étale, Zar}` as a morphism of topoi

Let `ε : S_étale → S_Zar` be the morphism of ringed sites of Stacks 070R, carried by the
continuous inclusion `AlgebraicGeometry.SmallEtale.opensToSmallEtale` of the small Zariski site
of a scheme `S` into its small étale site.  This module produces the underlying *morphism of
topoi* of `ε`, i.e. the adjoint pair `ε⁻¹ ⊣ ε_*` on sheaves of sets together with the left
exactness of `ε⁻¹`.

The two sites have different object universes — the opens of `S` form a `Type u` while the
small étale site is a `Type (u + 1)` — so `CategoryTheory.Functor.IsMorphismOfSites`, which is
available only for small categories in a single universe, cannot be used to produce it.  The
construction is carried out by hand instead, and it is the same one that
`AlgebraicGeometry.SmallEtale.inverseImageAuxAdjunction` performs for sheaves of commutative
rings: taking the image open is a functor `S_étale ⥤ S_Zar` left adjoint to the inclusion, so
precomposition with the opposite of the image-open functor is left adjoint to restriction along
`(opensToSmallEtale)ᵒᵖ`, and composing with sheafification exhibits a left adjoint of `ε_*`.
Left exactness is then read off that model: restriction along a functor preserves all limits
that exist pointwise, the inclusion of sheaves into presheaves creates limits, and
sheafification of `Type u`-valued presheaves is left exact because the small étale site is
essentially small.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toposInverseImageAux`: the sheafification of
  `F ↦ (V ↦ F(\mathrm{im}\, V))`, a model of `ε⁻¹` on sheaves of sets.
* `AlgebraicGeometry.SmallEtale.toposInverseImage`: `ε⁻¹` on sheaves of sets, as the chosen
  left adjoint of `ε_*`.
* `AlgebraicGeometry.SmallEtale.toZariskiMorphismOfTopoi`: the morphism of topoi underlying
  `ε`.

## Main results

* `AlgebraicGeometry.SmallEtale.toposInverseImageAuxIso`: the two models of `ε⁻¹` agree, both
  being left adjoint to `ε_*`.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_toposInverseImage`: `ε⁻¹` is left exact
  on sheaves of sets.  This is the substantive condition for `ε` to be a morphism of topoi.

## Implementation notes

`HasSheafify (topology B S hS) (Type u)` is obtained from essential smallness of the small
étale site, exactly as `AlgebraicGeometry.SmallEtale.hasSheafify_commRing` is for
`CommRingCat.{u}`; Mathlib's unconditional instance only gives sheafification of
`Type (u + 1)`-valued presheaves there, the site living one universe up.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Presheaves of sets valued in `Type u` on the small étale site of `S` have a left exact
sheafification, the site being essentially small.  Mathlib's unconditional instance produces
sheafification of `Type (u + 1)`-valued presheaves only, the objects of the site forming a
`Type (u + 1)`.

The coefficients here are one universe *below* the objects of the site, which is what
distinguishes this from `AlgebraicGeometry.SmallEtale.hasSheafify_type` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/ConstructibleAscendingChain.lean`,
the `Type (u + 1)`-valued statement. -/
public instance hasSheafify_smallType : HasSheafify (topology B S hS) (Type u) :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-! ### A model of `ε⁻¹` on sheaves of sets -/

/-- Sheafification of `V ↦ F(\mathrm{im}\, V)`, as a functor of the sheaf of sets `F` on the
small Zariski site of `S` whose sections over the image opens are taken.

This is the model of `ε⁻¹` built from `AlgebraicGeometry.SmallEtale.imageOpenAdjunction`; it is
identified with `toposInverseImage` by `toposInverseImageAuxIso`. -/
public noncomputable def toposInverseImageAux :
    Sheaf (Opens.grothendieckTopology ↥S) (Type u) ⥤ Sheaf (topology B S hS) (Type u) :=
  sheafToPresheaf (Opens.grothendieckTopology ↥S) (Type u) ⋙
    (whiskeringLeft _ _ _).obj (imageOpenFunctor B S hS).op ⋙
      presheafToSheaf (topology B S hS) (Type u)

/-- **Sheafifying `V ↦ F(\mathrm{im}\, V)` is left adjoint to the pushforward of sheaves of sets
along the inclusion of the small Zariski site of `S`.**  This is
`AlgebraicGeometry.SmallEtale.inverseImageAuxAdjunction` with `Type u` in place of
`CommRingCat.{u}`. -/
public noncomputable def toposInverseImageAuxAdjunction :
    toposInverseImageAux B S hS ⊣
      (opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  ((Adjunction.whiskerLeft (Type u) (imageOpenAdjunction B S hS).op).comp
      (sheafificationAdjunction (topology B S hS) (Type u))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (FullyFaithful.id _)
    (Iso.refl (sheafToPresheaf (Opens.grothendieckTopology ↥S) (Type u) ⋙
      ((whiskeringLeft _ _ _).obj (imageOpenFunctor B S hS).op ⋙
        presheafToSheaf (topology B S hS) (Type u))))
    (Iso.refl _)

/-- The pushforward of sheaves of sets along the inclusion of the small Zariski site of `S` into
the small étale site has a left adjoint, namely `toposInverseImageAux`. -/
public instance isRightAdjoint_sheafPushforwardContinuous_type :
    ((opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology ↥S) (topology B S hS)).IsRightAdjoint :=
  (toposInverseImageAuxAdjunction B S hS).isRightAdjoint

/-! ### `ε⁻¹` on sheaves of sets -/

/-- **`ε⁻¹` on sheaves of sets**, for `ε = id_{small, étale, Zar}`: the pullback of sheaves
along the continuous inclusion of the small Zariski site of `S` into the small étale site. -/
public noncomputable def toposInverseImage :
    Sheaf (Opens.grothendieckTopology ↥S) (Type u) ⥤ Sheaf (topology B S hS) (Type u) :=
  (opensToSmallEtale B S hS).sheafPullback (Type u)
    (Opens.grothendieckTopology ↥S) (topology B S hS)

/-- `ε⁻¹` is left adjoint to `ε_*` on sheaves of sets. -/
public noncomputable def toposAdjunction :
    toposInverseImage B S hS ⊣
      (opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  Functor.sheafAdjunctionContinuous _ _ _ _

/-- **`ε⁻¹` is sheafification of the sections over the image opens**, on sheaves of sets.  Both
are left adjoint to the pushforward of sheaves of sets along the inclusion of the small Zariski
site of `S`, and a left adjoint is unique up to canonical isomorphism. -/
public noncomputable def toposInverseImageAuxIso :
    toposInverseImageAux B S hS ≅ toposInverseImage B S hS :=
  Adjunction.leftAdjointUniq (toposInverseImageAuxAdjunction B S hS) (toposAdjunction B S hS)

/-- The model of `ε⁻¹` is left exact: restriction along `(imageOpenFunctor)ᵒᵖ` preserves the
pointwise limits of presheaves, the inclusion of sheaves into presheaves creates limits, and
sheafification of `Type u`-valued presheaves on the small étale site is left exact. -/
public instance preservesFiniteLimits_toposInverseImageAux :
    PreservesFiniteLimits (toposInverseImageAux B S hS) :=
  have : PreservesFiniteLimits ((whiskeringLeft (SmallEtale B S hS)ᵒᵖ (S.Opens)ᵒᵖ
      (Type u)).obj (imageOpenFunctor B S hS).op ⋙
      presheafToSheaf (topology B S hS) (Type u)) :=
    comp_preservesFiniteLimits _ _
  comp_preservesFiniteLimits _ _

/-- **`ε⁻¹` is left exact on sheaves of sets.**  This is the condition of Stacks 00XA that makes
the adjoint pair `ε⁻¹ ⊣ ε_*` a morphism of topoi, and the condition of Stacks 00X1 that makes
`ε` a morphism of sites. -/
public instance preservesFiniteLimits_toposInverseImage :
    PreservesFiniteLimits (toposInverseImage B S hS) :=
  preservesFiniteLimits_of_natIso (toposInverseImageAuxIso B S hS)

/-! ### The morphism of topoi -/

/-- **The morphism of topoi underlying `ε = id_{small, étale, Zar} : S_étale → S_Zar`**: the
adjoint pair `ε⁻¹ ⊣ ε_*` on sheaves of sets, whose inverse image is left exact.

The source of the morphism is the topos of the small étale site and its target the topos of the
small Zariski site, so the pushforward goes from the étale side to the Zariski side. -/
@[sga "4 VII 4.2.2"]
public noncomputable def toZariskiMorphismOfTopoi :
    MorphismOfTopoi (ringedTopos B S hS).Topos S.zariskiRingedTopos.Topos where
  pushforward := (opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology ↥S) (topology B S hS)
  inverseImage := toposInverseImage B S hS
  adj := toposAdjunction B S hS
  preservesFiniteLimits := preservesFiniteLimits_toposInverseImage B S hS

/-- `toZariskiMorphismOfTopoi` with its two sheaf categories spelled out rather than named
through `AlgebraicGeometry.RingedTopos.Topos`.  This is the spelling the transported inverse
image and direct image of sheaves of commutative rings unify against, the universes of the two
sites being different and solved for from the shape of the type. -/
@[sga "4 VII 4.2.2"]
public noncomputable abbrev toposHom :
    MorphismOfTopoi (Sheaf (topology B S hS) (Type u))
      (Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :=
  toZariskiMorphismOfTopoi B S hS

/-- The pushforward of `toZariskiMorphismOfTopoi` is the pushforward of sheaves of sets along
the continuous functor `opensToSmallEtale`. -/
@[simp]
public theorem toZariskiMorphismOfTopoi_pushforward :
    (toZariskiMorphismOfTopoi B S hS).pushforward =
      (opensToSmallEtale B S hS).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology ↥S) (topology B S hS) := rfl

/-- The inverse image of `toZariskiMorphismOfTopoi` is `toposInverseImage`. -/
@[simp]
public theorem toZariskiMorphismOfTopoi_inverseImage :
    (toZariskiMorphismOfTopoi B S hS).inverseImage = toposInverseImage B S hS := rfl

/-- The adjunction of `toZariskiMorphismOfTopoi` is `toposAdjunction`. -/
@[simp]
public theorem toZariskiMorphismOfTopoi_adj :
    (toZariskiMorphismOfTopoi B S hS).adj = toposAdjunction B S hS := rfl

end AlgebraicGeometry.SmallEtale

end
