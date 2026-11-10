module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatInverseImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleInverseImageReflectsZero
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSmallModel
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The flatness of `ε`, in the inverse-image form a morphism of ringed topoi asks for

Stacks 0GNA — the first assertion of Stacks 08H8 — says that the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 08H7 is flat.  It is in the library, as
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`, for the structure map
spelled `AlgebraicGeometry.SmallEtale.inverseImageStructureMap`, whose source is the sheaf
pullback of commutative rings along the *site* functor.

The exactness criterion
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` asks for the same flatness
with the source spelled as the *topos* inverse image
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor`, that is for
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage` of the morphism of ringed topoi attached to
`ε`.  The two morphisms of sheaves of commutative rings are not definitionally equal — `rfl`
fails — and this file identifies them and transports the flatness.

## The identification

Both sources are left adjoints of the pushforward of sheaves of commutative rings along `ε`, read
in the two presentations: the topos one has
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor` as right adjoint, the site one
`CategoryTheory.Functor.sheafPushforwardContinuous`.  Those two right adjoints are naturally
isomorphic by `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, which is the identity on
underlying sheaves of sets, so uniqueness of left adjoints identifies the two sources; and both
structure maps are the transpose of the one morphism
`AlgebraicGeometry.SmallEtale.commRingStructureMap`, so the identification carries one to the
other.

Flatness is then transported through the fibres.  It cannot be transported by
`AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso`, which asks the objects, the morphisms and
the sections of the site to share one universe while the small étale site has its objects one
universe above; so Stacks 05VC is used instead, in the form
`Stacks.isFlatMapULift_iff_forall_flat`, which reads flatness off the fibres at a conservative
family of points.  At each point the two fibres differ by the ring isomorphism the identification
induces, and a flat ring map stays flat after composition with an isomorphism.

## Main definitions

* `AlgebraicGeometry.SmallEtale.pushforwardCommRingIso`: the two pushforwards of sheaves of
  commutative rings along `ε` agree.
* `AlgebraicGeometry.SmallEtale.inverseImageCommRingToposAdjunction`: the topos inverse image of
  sheaves of commutative rings along `ε` is left adjoint to the site pushforward.
* `AlgebraicGeometry.SmallEtale.inverseImageCommRingToposIso`: **the two models of `ε⁻¹` on
  sheaves of commutative rings agree.**

## Main results

* `AlgebraicGeometry.SmallEtale.isConservativeFamilyOfPoints_uliftGeometricPointSitePoint`: the
  universe lifts of the geometric points of `S` are a conservative family of points of the small
  étale site, which is the shape Stacks 05VC consumes.
* `SmallEtale.inverseImageCommRingToposIso_hom_app_comp_inverseImageStructureMap`: the
  identification of the two models of `ε⁻¹` carries the site-pullback structure map to the
  inverse-image structure map of the morphism of ringed topoi.
* `AlgebraicGeometry.SmallEtale.isFlatMapULift_fSharpInverseImage_toZariskiRingedSiteHom`:
  **Stacks 0GNA at the morphism of ringed topoi attached to `ε`.**  This is the hypothesis
  `hflat` of `exactFunctor_pullbackModules_toZariskiRingedSiteHom`.

## Implementation notes

No `@[stacks]` attribute is claimed.  Stacks 0GNA and the flatness clause of 08H8 are registered
on `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`; this file restates that
one assertion at another spelling of the same morphism and proves no new clause of either tag.

## References

* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sheaves of sets valued in the universe of the sections -/

/-- The comma categories indexing the right Kan extension along the comparison of the small étale
site with its small model have limits of sets in the universe of the sections, being essentially
small in it. -/
public instance hasLimitsOfShape_structuredArrow_smallModel_inverse_op
    (W : (SmallEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow W (equivSmallModel.{u} (SmallEtale B S hS)).inverse.op) (Type u) :=
  inferInstance

/-! ### The geometric points, lifted -/

/-- **The universe lifts of the geometric points of `S` form a conservative family of points of
the small étale site.**

`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints` is the family of points
relative to the universe `u` of the sections; Stacks 05VC in the form
`Stacks.isFlatMapULift_iff_forall_flat` reads flatness after lifting the sections into a universe
containing the site, and so asks for conservativity of the lifted points, relative to `u + 1`.
The lift is `CategoryTheory.GrothendieckTopology.Point.ulift` and conservativity survives it
because the family is indexed by the points of the underlying space of `S`, hence is `u`-small. -/
public theorem isConservativeFamilyOfPoints_uliftGeometricPointSitePoint :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun x : ↥S =>
        (geometricPointSitePoint B S hS (.ofPoint S x)).ulift.{u + 1})) :=
  (GrothendieckTopology.isConservativeFamily_iff_ofObj _).1
    (GrothendieckTopology.IsConservativeFamily.ulift.{u + 1}
      ((GrothendieckTopology.isConservativeFamily_iff_ofObj _).2
        (isConservativeFamilyOfPoints_geometricSitePoints B S hS)))

/-! ### The two models of `ε⁻¹` on sheaves of commutative rings -/

/-- **The two pushforwards of sheaves of commutative rings along `ε` agree.**  The direct image
along the morphism of topoi underlying `ε` is restriction along the inclusion of the small Zariski
site, so transporting the commutative-ring structure along the former gives the latter; the
comparison is `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, the identity on underlying
sheaves of sets, and it is natural. -/
public def pushforwardCommRingIso :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u}
        (toZariskiRingedSiteHom B S hS).toRingedToposHom.toToposHom ≅
      (opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  NatIso.ofComponents
    (fun O => restrictionCommRingIso (Opens.grothendieckTopology ↥S) (topology B S hS)
      (opensToSmallEtale B S hS) O)
    (fun a => restrictionCommRingIso_naturality (Opens.grothendieckTopology ↥S)
      (topology B S hS) (opensToSmallEtale B S hS) a)

/-- The topos inverse image of sheaves of commutative rings along `ε` is left adjoint to the
*site* pushforward: it is left adjoint to the topos pushforward by Stacks 00YV, and the two
pushforwards agree by `AlgebraicGeometry.SmallEtale.pushforwardCommRingIso`. -/
public def inverseImageCommRingToposAdjunction :
    inverseImageCommRingFunctor.{u, u, u, u + 1, u, u}
        (toZariskiRingedSiteHom B S hS).toRingedToposHom.toToposHom ⊣
      (opensToSmallEtale B S hS).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  (commRingImageAdjunction
    (toZariskiRingedSiteHom B S hS).toRingedToposHom.toToposHom).ofNatIsoRight
      (pushforwardCommRingIso B S hS)

/-- **The two models of `ε⁻¹` on sheaves of commutative rings agree.**  The topos inverse image
along the morphism of topoi underlying `ε` and the sheaf pullback
`AlgebraicGeometry.SmallEtale.inverseImageCommRing` along the site functor are both left adjoints
of the pushforward along the inclusion of the small Zariski site, so they are identified by
uniqueness of left adjoints. -/
public def inverseImageCommRingToposIso :
    inverseImageCommRingFunctor.{u, u, u, u + 1, u, u}
        (toZariskiRingedSiteHom B S hS).toRingedToposHom.toToposHom ≅
      inverseImageCommRing B S hS :=
  Adjunction.leftAdjointUniq (inverseImageCommRingToposAdjunction B S hS)
    (inverseImageCommRingAdjunction B S hS)

/-- Two left adjoints of one right adjoint carry the same transpose to each other: the comparison
of the left adjoints, followed by the transpose taken in the second adjunction, is the transpose
taken in the first.

This is the computation behind
`AlgebraicGeometry.SmallEtale.inverseImageAuxIso_hom_app_comp_inverseImageStructureMap`, stated
once for an arbitrary pair of adjunctions rather than inlined. -/
private theorem leftAdjointUniq_hom_app_comp_homEquiv_symm
    {C₀ : Type*} [Category C₀] {D₀ : Type*} [Category D₀] {F F' : C₀ ⥤ D₀} {G : D₀ ⥤ C₀}
    (adj : F ⊣ G) (adj' : F' ⊣ G) {A : C₀} {T : D₀} (h : A ⟶ G.obj T) :
    (Adjunction.leftAdjointUniq adj adj').hom.app A ≫ (adj'.homEquiv A T).symm h
      = (adj.homEquiv A T).symm h := by
  refine (Adjunction.homEquiv_apply_eq _ _ _).1 ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_leftAdjointUniq_hom_app_assoc]
  rw [← Adjunction.homEquiv_unit]
  exact Equiv.apply_symm_apply _ _

/-- The inverse-image structure map of the morphism of ringed topoi attached to `ε` is the
transpose of `AlgebraicGeometry.SmallEtale.commRingStructureMap` in the adjunction
`AlgebraicGeometry.SmallEtale.inverseImageCommRingToposAdjunction`.

The structure map of that morphism of ringed topoi is `commRingStructureMap` followed by
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`, and transposing it in the topos adjunction
is, by `CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_symm_apply`, the same as transposing
`commRingStructureMap` itself in the adjunction obtained by transporting along that comparison. -/
private theorem homEquiv_symm_commRingStructureMap :
    ((inverseImageCommRingToposAdjunction B S hS).homEquiv S.zariskiCommRingSheaf
        (commRingStructureSheaf B S hS)).symm (commRingStructureMap B S hS)
      = (toZariskiRingedSiteHom B S hS).toRingedToposHom.fSharpInverseImage :=
  Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ _

/-- **The identification of the two models of `ε⁻¹` carries one structure map to the other.**  The
structure map `AlgebraicGeometry.SmallEtale.inverseImageStructureMap` and the inverse-image
structure map of the morphism of ringed topoi attached to `ε` are both the transpose of
`AlgebraicGeometry.SmallEtale.commRingStructureMap`, in the two adjunctions whose left adjoints
`AlgebraicGeometry.SmallEtale.inverseImageCommRingToposIso` compares. -/
public theorem inverseImageCommRingToposIso_hom_app_comp_inverseImageStructureMap :
    ((inverseImageCommRingToposIso B S hS).app S.zariskiCommRingSheaf).hom ≫
        inverseImageStructureMap B S hS
      = (toZariskiRingedSiteHom B S hS).toRingedToposHom.fSharpInverseImage :=
  (leftAdjointUniq_hom_app_comp_homEquiv_symm (inverseImageCommRingToposAdjunction B S hS)
    (inverseImageCommRingAdjunction B S hS) (commRingStructureMap B S hS)).trans
    (homEquiv_symm_commRingStructureMap B S hS)

/-! ### Transporting the flatness -/

/-- A flat ring map stays flat after composition with an isomorphism of sheaves of commutative
rings, read at the fibre of a point: the fibre of an isomorphism is an isomorphism, hence
bijective, hence flat, and flatness is stable under composition. -/
private theorem flat_presheafFiber_map_comp_iso (Φ : (topology B S hS).Point.{u})
    {O O' T : Sheaf (topology B S hS) CommRingCat.{u}} (a : O ≅ O') (g : O' ⟶ T)
    (hg : ((Φ.presheafFiber (A := CommRingCat.{u})).map g.hom).hom.Flat) :
    ((Φ.presheafFiber (A := CommRingCat.{u})).map (a.hom ≫ g).hom).hom.Flat := by
  have he : (a.hom ≫ g).hom = a.hom.hom ≫ g.hom := rfl
  rw [he, Functor.map_comp, CommRingCat.hom_comp]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective ?_) hg
  exact ConcreteCategory.bijective_of_isIso
    (((Φ.presheafFiber (A := CommRingCat.{u})).mapIso
      ((sheafToPresheaf (topology B S hS) CommRingCat.{u}).mapIso a)).hom)

/-- **Stacks 0GNA at the morphism of ringed topoi attached to `ε`.**  The inverse-image form
`ε⁻¹𝒪_{S_Zar} ⟶ 𝒪_{S_étale}` of the structure map of `ε`, with the source taken to be the *topos*
inverse image of `𝒪_{S_Zar}`, is a flat morphism of sheaves of commutative rings.

This is `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap` at the
other spelling of the same morphism.  The two are identified by
`inverseImageCommRingToposIso_hom_app_comp_inverseImageStructureMap`, and the flatness is carried
across through the fibres at the geometric points of `S`, by Stacks 05VC in the form
`Stacks.isFlatMapULift_iff_forall_flat`.

It is the hypothesis `hflat` of
`AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariskiRingedSiteHom`, and so the
whole of what the exactness assertion of Stacks 08H8 still needed on the flatness side. -/
public theorem isFlatMapULift_fSharpInverseImage_toZariskiRingedSiteHom :
    SheafOfModules.IsFlatMapULift.{u, u + 1, u}
      (toZariskiRingedSiteHom B S hS).toRingedToposHom.fSharpInverseImage := by
  have iff_flat : ∀ {O O' : Sheaf (topology B S hS) CommRingCat.{u}} (g : O ⟶ O'), _ ↔ _ :=
    Stacks.isFlatMapULift_iff_forall_flat
      (fun x : ↥S => geometricPointSitePoint B S hS (.ofPoint S x))
      (isConservativeFamilyOfPoints_uliftGeometricPointSitePoint B S hS)
  rw [← inverseImageCommRingToposIso_hom_app_comp_inverseImageStructureMap B S hS]
  exact (iff_flat _).2 fun i => flat_presheafFiber_map_comp_iso B S hS _ _ _
    ((iff_flat _).1 (isFlatMapULift_inverseImageStructureMap B S hS) i)

end AlgebraicGeometry.SmallEtale

end
