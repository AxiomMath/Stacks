module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged

/-!
# Functoriality of the structure sheaf on fibred groupoids

Let `p : 𝒳 ⥤ (Sch/S)_fppf` and `q : 𝒴 ⥤ (Sch/S)_fppf` be categories fibred in groupoids, let
`F : 𝒳 ⥤ 𝒴` be a 1-morphism over the site, and let `τ` be one of the five inherited topologies.
The inverse image of the structure sheaf of `𝒴` along `F` is the structure sheaf of `𝒳`, on the
nose, and that identification turns the induced morphism of topoi into a morphism of ringed
topoi.

## Main definitions

* `AlgebraicGeometry.FibredSite.associatedRingedTopos`: the associated site of a category fibred
  in groupoids together with its structure sheaf, as a ringed topos.
* `AlgebraicGeometry.FibredSite.directImageAdjunction`: the direct image right adjoint to
  restriction of sheaves of sets along a 1-morphism, as an adjunction.
* `AlgebraicGeometry.FibredSite.ringedToposMorphism`: the morphism of ringed topoi induced by a
  1-morphism.

## Main results

* `AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`: the canonical identification of
  structure sheaves.
* `AlgebraicGeometry.FibredSite.ringedToposMorphism_inverseImage`: the underlying geometric
  morphism of `ringedToposMorphism` is the one `F` induces, its inverse image being restriction
  along `F`.
* `AlgebraicGeometry.FibredSite.ringedToposMorphism_fSharpInverseImage`: its structure map is the
  canonical identification itself.
* `AlgebraicGeometry.FibredSite.ringedToposMorphism_isIso_fSharpInverseImage`: that structure map
  is an isomorphism.

## Implementation notes

Inverse image is `Functor.sheafPushforwardContinuous`, restriction along `F` for the inherited
topologies. The statements about the morphism of ringed topoi assume
`[∀ G, F.op.HasPointwiseRightKanExtension G]`, the existence of the right Kan extensions along
`F.op` that form the direct image.

## References

* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.FibredSite

universe u v w v' w'

/-- For a 1-morphism `F` of categories fibred in groupoids over the big fppf site, the inverse
image along `F` of the structure sheaf of the target is the structure sheaf of the source, as a
sheaf of commutative rings and on the nose. -/
@[stacks 06TW "canonical identification of structure sheaves"]
theorem inverseImageStructureSheaf_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind) :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    (F.sheafPushforwardContinuous CommRingCat.{u}
      (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ)).obj
        (FibredSite.structureSheaf B S hS q hq τ) =
      FibredSite.structureSheaf B S hS p hp τ := by
  obtain ⟨rfl, _⟩ := hF; ext; rfl

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- The ringed topos of a category fibred in groupoids for one of the five inherited
topologies: the associated site `AlgebraicGeometry.BigFppfOver.associatedTopology`, carrying the
structure sheaf `AlgebraicGeometry.FibredSite.structureSheaf`. -/
noncomputable def associatedRingedTopos
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : SiteKind) : RingedTopos.{w, v, u} where
  C := X
  J := BigFppfOver.associatedTopology B S hS p τ
  O := FibredSite.structureSheaf B S hS p hp τ

/-- The direct image of sheaves of sets along a 1-morphism of categories fibred in groupoids,
presented by its adjunction with restriction: the right Kan extension along `F.op`, taken on
sheaves for the two inherited topologies. -/
noncomputable def directImageAdjunction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind)
    [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G] :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    Σ' G : Sheaf (BigFppfOver.associatedTopology B S hS p τ) (Type u) ⥤
        Sheaf (BigFppfOver.associatedTopology B S hS q τ) (Type u),
      F.sheafPushforwardContinuous (Type u)
        (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ) ⊣ G := by
  let := hp.isFibered
  let := hq.isFibered
  let J := (B.baseTopology τ).over (B.obj hS)
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology J).1
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology J).2
  exact ⟨F.sheafPushforwardCocontinuous (Type u)
      (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ),
    hF.sheafAdjunctionInheritedTopology J (Type u)⟩

/-- A 1-morphism `F` of categories fibred in groupoids over the big fppf site induces a morphism
of ringed topoi in the sense of `AlgebraicGeometry.RingedToposHom`, between the two associated
ringed topoi: the underlying morphism of topoi is the one `F` induces, and its structure map is
the adjoint of the canonical identification
`AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`. -/
@[stacks 06TW "morphism of ringed topoi"]
noncomputable def ringedToposMorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind)
    [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G] :
    RingedToposHom
      (associatedRingedTopos B S hS p hp τ)
      (associatedRingedTopos B S hS q hq τ) := by
  let J := BigFppfOver.associatedTopology B S hS p τ
  let K := BigFppfOver.associatedTopology B S hS q τ
  let := hp.isFibered
  let := hq.isFibered
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).2
  let d := directImageAdjunction B S hS p q hp hq F hF τ
  let f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)) :=
    { inverseImage := F.sheafPushforwardContinuous (Type u) J K
      pushforward := d.1
      adj := d.2
      preservesFiniteLimits := hF.preservesFiniteLimits_inverseImage
        ((B.baseTopology τ).over (B.obj hS)) (Type u) }
  exact
    { toToposHom := f
      fSharp := (commRingImageAdjunction f).homEquiv _ _
        ((restrictionCommRingIso J K F
          (FibredSite.structureSheaf B S hS q hq τ)).hom ≫
          eqToHom (inverseImageStructureSheaf_eq B S hS p q hp hq F hF τ)) }

/-- The morphism of ringed topoi `AlgebraicGeometry.FibredSite.ringedToposMorphism` sits over
the morphism of topoi that `F` itself induces: its inverse image is restriction of sheaves along
`F` for the two inherited topologies. -/
@[stacks 06TW "inverse image of the underlying geometric morphism"]
theorem ringedToposMorphism_inverseImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind)
    [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G] :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    (ringedToposMorphism B S hS p q hp hq F hF τ).toToposHom.inverseImage =
      F.sheafPushforwardContinuous (Type u)
        (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ) := rfl

/-- The inverse-image form of the structure map of
`AlgebraicGeometry.FibredSite.ringedToposMorphism` is the canonical identification itself: the
comparison of the inverse image of a sheaf of commutative rings with its restriction, followed
by the equality `AlgebraicGeometry.FibredSite.inverseImageStructureSheaf_eq`. -/
@[stacks 06TW "canonical structure map"]
theorem ringedToposMorphism_fSharpInverseImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind)
    [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G] :
    letI := hp.isFibered
    letI := hq.isFibered
    letI := (hF.isContinuous_and_isCocontinuous_inheritedTopology
      ((B.baseTopology τ).over (B.obj hS))).1
    (ringedToposMorphism B S hS p q hp hq F hF τ).fSharpInverseImage =
      (restrictionCommRingIso
        (BigFppfOver.associatedTopology B S hS p τ)
        (BigFppfOver.associatedTopology B S hS q τ) F
        (FibredSite.structureSheaf B S hS q hq τ)).hom ≫
        eqToHom (inverseImageStructureSheaf_eq B S hS p q hp hq F hF τ) := by
  let := hp.isFibered
  let := hq.isFibered
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  let m := ringedToposMorphism B S hS p q hp hq F hF τ
  let e := (commRingImageAdjunction m.toToposHom).homEquiv
    (FibredSite.structureSheaf B S hS q hq τ)
    (FibredSite.structureSheaf B S hS p hp τ)
  let x := (restrictionCommRingIso
      (BigFppfOver.associatedTopology B S hS p τ)
      (BigFppfOver.associatedTopology B S hS q τ) F
      (FibredSite.structureSheaf B S hS q hq τ)).hom ≫
    eqToHom (inverseImageStructureSheaf_eq B S hS p q hp hq F hF τ)
  exact Equiv.symm_apply_apply e x

/-- The inverse-image form of the structure map of
`AlgebraicGeometry.FibredSite.ringedToposMorphism` is an isomorphism. -/
@[stacks 06TW "canonical identification gives an isomorphism of structure sheaves"]
theorem ringedToposMorphism_isIso_fSharpInverseImage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
    (p : X ⥤ BigFppfOver B S hS)
    (q : Y ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (F : X ⥤ Y) (hF : p.IsFibredOneMorphism q F)
    (τ : SiteKind)
    [∀ (G : Xᵒᵖ ⥤ Type u), F.op.HasPointwiseRightKanExtension G] :
    IsIso (ringedToposMorphism B S hS p q hp hq F hF τ).fSharpInverseImage := by
  let := hp.isFibered
  let := hq.isFibered
  let := (hF.isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1
  rw [ringedToposMorphism_fSharpInverseImage]
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (eqToIso (inverseImageStructureSheaf_eq B S hS p q hp hq F hF τ)).isIso_hom

end AlgebraicGeometry.FibredSite

end
