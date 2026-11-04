module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.SmallAffineDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing

/-!
# The ringed topos of a small affine site

Let `S` be a scheme and let `τ` be either the Zariski or the étale topology. The small affine
site `S_{affine, τ}` — the affine objects of the small site `S_τ`, with the standard `τ`
coverings — is a dense subsite of `S_τ`, so restriction of sheaves along the inclusion is an
equivalence of topoi `Sh(S_{affine, τ}) ⥤ Sh(S_τ)` (Stacks 0F1B and 04HR). Writing `𝒪` for
the structure sheaf `T ↦ Γ(T, 𝒪_T)` of `S_τ` and `𝒪_affine` for its restriction, this file
upgrades that equivalence to an equivalence of *ringed* topoi
`(Sh(S_{affine, τ}), 𝒪_affine) ⟶ (Sh(S_τ), 𝒪)`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.ringedTopos` and
  `AlgebraicGeometry.SmallAffineZariski.ringedTopos`: the two small Zariski sites with their
  structure sheaves of commutative rings, the second being the restriction of the first.
* `AlgebraicGeometry.SmallEtale.ringedTopos` and
  `AlgebraicGeometry.SmallAffineEtale.ringedTopos`: the same for the étale topology.
* `AlgebraicGeometry.SmallAffineZariski.ringedToposHom` and
  `AlgebraicGeometry.SmallAffineEtale.ringedToposHom`: the morphism of ringed topoi.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.ringedToposHom_inverseImage` and its étale counterpart:
  the inverse image of the underlying morphism of topoi is restriction along the inclusion of
  the affine objects.
* `AlgebraicGeometry.SmallAffineZariski.ringedToposHom_inverseImage_isEquivalence` and its
  étale counterpart: that inverse image is an equivalence, so the morphism of topoi is an
  equivalence of topoi.
* `AlgebraicGeometry.SmallAffineZariski.isIso_ringedToposHom_fSharpInverseImage` and its étale
  counterpart: the structure morphism `g⁻¹𝒪 ⟶ 𝒪_affine` is an isomorphism, so the morphism of
  ringed topoi is an equivalence of ringed topoi.
* `AlgebraicGeometry.SmallAffineZariski.ringedToposHom_fSharpInverseImage_forget` and its étale
  counterpart: that structure morphism is the canonical one, being the identity on underlying
  sheaves of sets.

## Implementation notes

The structure sheaf of a small site is taken with values in `CommRingCat`, since
`AlgebraicGeometry.RingedTopos` does; the sheaf condition is the one already proved for the
`RingCat`-valued presheaf of global functions (Stacks 03DU), transported back along the
limit-reflecting functor `forget₂ CommRingCat RingCat`.

The structure sheaf of the small affine site is *defined* to be the restriction of the
structure sheaf of the small site, which is what the source says it is; the identification of
that restriction with the presheaf of global functions on the affine objects is then true by
definition, and is recorded as
`AlgebraicGeometry.SmallAffineZariski.ringedTopos_O_obj`.

The morphism of topoi takes the restriction functor as its inverse image, and the cocontinuous
partner of restriction as its direct image; the adjunction is Mathlib's
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`, so "the pullback functor is given by
restriction" holds on the nose rather than up to a comparison. The direct image is a right Kan
extension along the inclusion, which exists because the small affine sites are essentially
small.

The structure morphism of the morphism of ringed topoi is the adjunct of the identification
`g⁻¹𝒪 ≅ 𝒪_affine` of `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`: transporting the
ring operations of `𝒪` along restriction gives the ring operations of the restriction of `𝒪`,
and the identification is the identity on underlying sheaves of sets. The morphism of ringed
topoi is an `AlgebraicGeometry.RingedToposHom`, whose structure morphism is the direct-image form
`f♯ : 𝒪 ⟶ g_*𝒪_affine` and whose inverse-image form is derived from it.

## References

* [Stacks Project, Tag 0GZW](https://stacks.math.columbia.edu/tag/0GZW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry

/-! ### The Zariski case -/

namespace SmallAffineZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the small affine Zariski site exhibits it as a dense subsite of the small
Zariski site, by Stacks 0F1B. -/
public instance inclusion_isDenseSubsite :
    (inclusion B S hS).IsDenseSubsite (topology B S hS) (SmallZariski.topology B S hS) :=
  (inclusion_isSpecialCocontinuous B S hS).2

/-- Limits of the shape indexed by the affine objects over a given object of the small Zariski
site exist, because the small affine Zariski site is essentially small. This is what makes the
right Kan extension along the inclusion — the direct image of the induced morphism of topoi —
exist. -/
public instance hasLimitsOfShape_structuredArrow (X : (SmallZariski B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) (Type u) :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The same, for limits of commutative rings. -/
public instance hasLimitsOfShape_structuredArrow_commRingCat (X : (SmallZariski B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) CommRingCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall _ _

end SmallAffineZariski

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DU, small Zariski structure sheaf.** The presheaf of global functions on the
small Zariski site of `S`, with values in commutative rings, is a sheaf. -/
public theorem isSheaf_globalFunctions :
    Presheaf.IsSheaf (topology B S hS) ((toScheme B S hS).op ⋙ Scheme.Γ) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat.{u} RingCat.{u})
    (structure_isSheaf B S hS)

/-- The small Zariski site of `S` with its structure sheaf of commutative rings, the sheaf of
global functions `T ↦ Γ(T, 𝒪_T)`. -/
public def ringedTopos : RingedTopos.{u, u + 1, u} where
  C := SmallZariski B S hS
  J := topology B S hS
  O := ⟨(toScheme B S hS).op ⋙ Scheme.Γ, isSheaf_globalFunctions B S hS⟩

end SmallZariski

namespace SmallAffineZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small affine Zariski site of `S` with the restriction of the structure sheaf of the
small Zariski site as its structure sheaf. -/
public noncomputable def ringedTopos : RingedTopos.{u, u + 1, u} where
  C := SmallAffineZariski B S hS
  J := topology B S hS
  O := ((inclusion B S hS).sheafPushforwardContinuous CommRingCat.{u}
    (topology B S hS) (SmallZariski.topology B S hS)).obj (SmallZariski.ringedTopos B S hS).O

/-- The restricted structure sheaf is the sheaf of global functions on the affine objects. -/
@[simp]
public theorem ringedTopos_O_obj :
    (ringedTopos B S hS).O.obj = (toScheme B S hS).op ⋙ Scheme.Γ :=
  rfl

/-- The morphism of topoi `Sh(S_{affine, Zar}) ⟶ Sh(S_Zar)` induced by the inclusion of the
affine objects: its inverse image is restriction along that inclusion, and its direct image is
the right Kan extension, which is the cocontinuous partner of restriction. -/
public noncomputable def toposMorphism :
    MorphismOfTopoi (ringedTopos B S hS).Topos (SmallZariski.ringedTopos B S hS).Topos where
  inverseImage := (inclusion B S hS).sheafPushforwardContinuous (Type u)
    (topology B S hS) (SmallZariski.topology B S hS)
  pushforward := (inclusion B S hS).sheafPushforwardCocontinuous (Type u)
    (topology B S hS) (SmallZariski.topology B S hS)
  adj := (inclusion B S hS).sheafAdjunctionCocontinuous (Type u)
    (topology B S hS) (SmallZariski.topology B S hS)
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous
    (topology B S hS) (SmallZariski.topology B S hS) (inclusion B S hS) (Type u)

/-- The identification of the inverse image of the structure sheaf with the structure sheaf of
the small affine Zariski site: transporting the ring operations of `𝒪` along restriction gives
the ring operations of the restriction of `𝒪`. -/
public noncomputable def structureIso :
    (inverseImageCommRingFunctor (toposMorphism B S hS)).obj
        (SmallZariski.ringedTopos B S hS).O ≅ (ringedTopos B S hS).O :=
  restrictionCommRingIso (topology B S hS) (SmallZariski.topology B S hS)
    (inclusion B S hS) (SmallZariski.ringedTopos B S hS).O

/-- The morphism of ringed topoi `(Sh(S_{affine, Zar}), 𝒪_affine) ⟶ (Sh(S_Zar), 𝒪)` given by the
inclusion of the affine objects of the small Zariski site of `S`, with structure morphism the
adjunct of the identification of `g⁻¹𝒪` with the restriction `𝒪_affine` of `𝒪`. -/
@[stacks 0GZW "Zariski case"]
public noncomputable def ringedToposHom :
    RingedToposHom (ringedTopos B S hS) (SmallZariski.ringedTopos B S hS) where
  toToposHom := toposMorphism B S hS
  fSharp := (commRingImageAdjunction (toposMorphism B S hS)).homEquiv
    (SmallZariski.ringedTopos B S hS).O (ringedTopos B S hS).O (structureIso B S hS).hom

/-- The inverse image of the equivalence is restriction along the inclusion of the affine objects,
on the nose. -/
@[stacks 0GZW "Zariski case"]
public theorem ringedToposHom_inverseImage :
    (ringedToposHom B S hS).toToposHom.inverseImage =
      (inclusion B S hS).sheafPushforwardContinuous (Type u)
        (topology B S hS) (SmallZariski.topology B S hS) :=
  rfl

/-- The underlying morphism of topoi is an equivalence of topoi: its inverse image, restriction
along the inclusion of the affine objects, is an equivalence of categories of sheaves. -/
@[stacks 0GZW "Zariski case"]
public theorem ringedToposHom_inverseImage_isEquivalence :
    (ringedToposHom B S hS).toToposHom.inverseImage.IsEquivalence :=
  inferInstanceAs ((inclusion B S hS).sheafPushforwardContinuous (Type u)
    (topology B S hS) (SmallZariski.topology B S hS)).IsEquivalence

/-- The inverse-image form of the structure morphism is the identification of `g⁻¹𝒪` with
`𝒪_affine`. -/
public theorem ringedToposHom_fSharpInverseImage :
    (ringedToposHom B S hS).fSharpInverseImage = (structureIso B S hS).hom :=
  ((commRingImageAdjunction (toposMorphism B S hS)).homEquiv
    (SmallZariski.ringedTopos B S hS).O (ringedTopos B S hS).O).symm_apply_apply _

/-- The structure morphism `g⁻¹𝒪 ⟶ 𝒪_affine` is an isomorphism, so the morphism of ringed topoi is
an equivalence of ringed topoi and not merely a morphism whose underlying morphism of topoi is an
equivalence. -/
@[stacks 0GZW "Zariski case"]
public theorem isIso_ringedToposHom_fSharpInverseImage :
    IsIso (ringedToposHom B S hS).fSharpInverseImage :=
  (ringedToposHom_fSharpInverseImage B S hS) ▸ (structureIso B S hS).isIso_hom

/-- The structure morphism is the canonical one: on underlying sheaves of sets it is the identity
of the restriction of the underlying sheaf of sets of `𝒪`, so `𝒪_affine` really is `𝒪` restricted
and not an arbitrary sheaf of rings with the same underlying sheaf of sets. -/
@[stacks 0GZW "Zariski case"]
public theorem ringedToposHom_fSharpInverseImage_forget :
    (sheafCompose (topology B S hS) (forget CommRingCat.{u})).map
        (ringedToposHom B S hS).fSharpInverseImage =
      𝟙 ((inclusion B S hS).sheafPushforwardContinuous (Type u)
        (topology B S hS) (SmallZariski.topology B S hS) |>.obj
        ((sheafCompose (SmallZariski.topology B S hS) (forget CommRingCat.{u})).obj
          (SmallZariski.ringedTopos B S hS).O)) := by
  rw [ringedToposHom_fSharpInverseImage, structureIso]
  exact restrictionCommRingIso_hom_forget (topology B S hS) (SmallZariski.topology B S hS)
    (inclusion B S hS) (SmallZariski.ringedTopos B S hS).O

end SmallAffineZariski

/-! ### The étale case -/

namespace SmallAffineEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of the small affine étale site exhibits it as a dense subsite of the small
étale site, by Stacks 04HR. -/
public instance inclusion_isDenseSubsite :
    (inclusion B S hS).IsDenseSubsite (topology B S hS) (SmallEtale.topology B S hS) :=
  (inclusion_isSpecialCocontinuous B S hS).2

/-- Limits of the shape indexed by the affine objects over a given object of the small étale
site exist, because the small affine étale site is essentially small. This is what makes the
right Kan extension along the inclusion — the direct image of the induced morphism of topoi —
exist. -/
public instance hasLimitsOfShape_structuredArrow (X : (SmallEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) (Type u) :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- The same, for limits of commutative rings. -/
public instance hasLimitsOfShape_structuredArrow_commRingCat (X : (SmallEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (inclusion B S hS).op) CommRingCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall _ _

end SmallAffineEtale

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DU, small étale structure sheaf.** The presheaf of global functions on the small
étale site of `S`, with values in commutative rings, is a sheaf. -/
public theorem isSheaf_globalFunctions :
    Presheaf.IsSheaf (topology B S hS) ((toScheme B S hS).op ⋙ Scheme.Γ) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat.{u} RingCat.{u})
    (structure_isSheaf B S hS)

/-- The small étale site of `S` with its structure sheaf of commutative rings, the sheaf of
global functions `T ↦ Γ(T, 𝒪_T)`. -/
public def ringedTopos : RingedTopos.{u, u + 1, u} where
  C := SmallEtale B S hS
  J := topology B S hS
  O := ⟨(toScheme B S hS).op ⋙ Scheme.Γ, isSheaf_globalFunctions B S hS⟩

end SmallEtale

namespace SmallAffineEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small affine étale site of `S` with the restriction of the structure sheaf of the small
étale site as its structure sheaf. -/
public noncomputable def ringedTopos : RingedTopos.{u, u + 1, u} where
  C := SmallAffineEtale B S hS
  J := topology B S hS
  O := ((inclusion B S hS).sheafPushforwardContinuous CommRingCat.{u}
    (topology B S hS) (SmallEtale.topology B S hS)).obj (SmallEtale.ringedTopos B S hS).O

/-- The restricted structure sheaf is the sheaf of global functions on the affine objects. -/
@[simp]
public theorem ringedTopos_O_obj :
    (ringedTopos B S hS).O.obj = (toScheme B S hS).op ⋙ Scheme.Γ :=
  rfl

/-- The morphism of topoi `Sh(S_{affine, étale}) ⟶ Sh(S_étale)` induced by the inclusion of
the affine objects: its inverse image is restriction along that inclusion, and its direct image
is the right Kan extension, which is the cocontinuous partner of restriction. -/
public noncomputable def toposMorphism :
    MorphismOfTopoi (ringedTopos B S hS).Topos (SmallEtale.ringedTopos B S hS).Topos where
  inverseImage := (inclusion B S hS).sheafPushforwardContinuous (Type u)
    (topology B S hS) (SmallEtale.topology B S hS)
  pushforward := (inclusion B S hS).sheafPushforwardCocontinuous (Type u)
    (topology B S hS) (SmallEtale.topology B S hS)
  adj := (inclusion B S hS).sheafAdjunctionCocontinuous (Type u)
    (topology B S hS) (SmallEtale.topology B S hS)
  preservesFiniteLimits := Functor.preservesFiniteLimits_sheafPushforwardContinuous
    (topology B S hS) (SmallEtale.topology B S hS) (inclusion B S hS) (Type u)

/-- The identification of the inverse image of the structure sheaf with the structure sheaf of
the small affine étale site: transporting the ring operations of `𝒪` along restriction gives
the ring operations of the restriction of `𝒪`. -/
public noncomputable def structureIso :
    (inverseImageCommRingFunctor (toposMorphism B S hS)).obj
        (SmallEtale.ringedTopos B S hS).O ≅ (ringedTopos B S hS).O :=
  restrictionCommRingIso (topology B S hS) (SmallEtale.topology B S hS)
    (inclusion B S hS) (SmallEtale.ringedTopos B S hS).O

/-- The morphism of ringed topoi `(Sh(S_{affine, étale}), 𝒪_affine) ⟶ (Sh(S_étale), 𝒪)` given by
the inclusion of the affine objects of the small étale site of `S`, with structure morphism the
adjunct of the identification of `g⁻¹𝒪` with the restriction `𝒪_affine` of `𝒪`. -/
@[stacks 0GZW "étale case"]
public noncomputable def ringedToposHom :
    RingedToposHom (ringedTopos B S hS) (SmallEtale.ringedTopos B S hS) where
  toToposHom := toposMorphism B S hS
  fSharp := (commRingImageAdjunction (toposMorphism B S hS)).homEquiv
    (SmallEtale.ringedTopos B S hS).O (ringedTopos B S hS).O (structureIso B S hS).hom

/-- The inverse image of the equivalence is restriction along the inclusion of the affine objects,
on the nose. -/
@[stacks 0GZW "étale case"]
public theorem ringedToposHom_inverseImage :
    (ringedToposHom B S hS).toToposHom.inverseImage =
      (inclusion B S hS).sheafPushforwardContinuous (Type u)
        (topology B S hS) (SmallEtale.topology B S hS) :=
  rfl

/-- The underlying morphism of topoi is an equivalence of topoi: its inverse image, restriction
along the inclusion of the affine objects, is an equivalence of categories of sheaves. -/
@[stacks 0GZW "étale case"]
public theorem ringedToposHom_inverseImage_isEquivalence :
    (ringedToposHom B S hS).toToposHom.inverseImage.IsEquivalence :=
  inferInstanceAs ((inclusion B S hS).sheafPushforwardContinuous (Type u)
    (topology B S hS) (SmallEtale.topology B S hS)).IsEquivalence

/-- The inverse-image form of the structure morphism is the identification of `g⁻¹𝒪` with
`𝒪_affine`. -/
public theorem ringedToposHom_fSharpInverseImage :
    (ringedToposHom B S hS).fSharpInverseImage = (structureIso B S hS).hom :=
  ((commRingImageAdjunction (toposMorphism B S hS)).homEquiv
    (SmallEtale.ringedTopos B S hS).O (ringedTopos B S hS).O).symm_apply_apply _

/-- The structure morphism `g⁻¹𝒪 ⟶ 𝒪_affine` is an isomorphism, so the morphism of ringed topoi is
an equivalence of ringed topoi and not merely a morphism whose underlying morphism of topoi is an
equivalence. -/
@[stacks 0GZW "étale case"]
public theorem isIso_ringedToposHom_fSharpInverseImage :
    IsIso (ringedToposHom B S hS).fSharpInverseImage :=
  (ringedToposHom_fSharpInverseImage B S hS) ▸ (structureIso B S hS).isIso_hom

/-- The structure morphism is the canonical one: on underlying sheaves of sets it is the identity
of the restriction of the underlying sheaf of sets of `𝒪`, so `𝒪_affine` really is `𝒪` restricted
and not an arbitrary sheaf of rings with the same underlying sheaf of sets. -/
@[stacks 0GZW "étale case"]
public theorem ringedToposHom_fSharpInverseImage_forget :
    (sheafCompose (topology B S hS) (forget CommRingCat.{u})).map
        (ringedToposHom B S hS).fSharpInverseImage =
      𝟙 ((inclusion B S hS).sheafPushforwardContinuous (Type u)
        (topology B S hS) (SmallEtale.topology B S hS) |>.obj
        ((sheafCompose (SmallEtale.topology B S hS) (forget CommRingCat.{u})).obj
          (SmallEtale.ringedTopos B S hS).O)) := by
  rw [ringedToposHom_fSharpInverseImage, structureIso]
  exact restrictionCommRingIso_hom_forget (topology B S hS) (SmallEtale.topology B S hS)
    (inclusion B S hS) (SmallEtale.ringedTopos B S hS).O

end SmallAffineEtale

end AlgebraicGeometry

end
