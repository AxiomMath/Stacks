module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence

/-!
# Modules on the small étale site of a representable algebraic space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`.  The small
étale site of the algebraic space `yoneda.obj U` is equivalent to the small étale site of `T`
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`), and that equivalence *transports
the structure sheaf*: the sheaf of rings `V ↦ Γ(V, 𝒪_V)` on either site is the restriction of
the other along the equivalence.  Composing the associated-module functor of Stacks 03DU (4)
with that transport carries an `𝒪_T`-module on the Zariski site of `T` to an
`𝒪_{yoneda.obj U}`-module on the small étale site of the algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.ringStructureSheaf` is the structure sheaf of the small étale site
  of a presheaf with commutativity forgotten, the sheaf of rings in which
  `AlgebraicGeometry.Space.Modules` is indexed.
* `AlgebraicGeometry.Space.representedStructureMap` is the comparison of structure sheaves
  along the equivalence of sites, and
  `AlgebraicGeometry.Space.representedStructureMapInverse` the same comparison read along the
  inverse equivalence.
* `AlgebraicGeometry.Space.representedModulePushforward` and
  `AlgebraicGeometry.Space.representedModuleRestriction` transport sheaves of modules between
  the small étale site of `T` and the small étale site of `yoneda.obj U`.
* `AlgebraicGeometry.Space.representedAssociatedModule` is the resulting functor
  `𝒪_T`-modules `⥤` `𝒪_{yoneda.obj U}`-modules, and
  `AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso` identifies its value at
  `𝒪_T` with `𝒪_{yoneda.obj U}`.

## Main results

* `AlgebraicGeometry.Space.ringStructureSheaf_eq_ringSheaf`: the structure sheaf just named is
  the sheaf of rings of the small étale ringed site of the space, by `rfl`.
* `AlgebraicGeometry.Space.representedModulePushforward_obj_val_presheaf`: the transported
  module has, as a presheaf of abelian groups, the restriction of the original along the
  equivalence of sites.
* `AlgebraicGeometry.Space.additive_representedAssociatedModule`: the functor is additive.
* `SheafOfModules.additive_pushforward`: the pushforward of sheaves of modules along a
  continuous functor is additive.

## Implementation notes

The comparison of structure sheaves is the identity: both sites assign to an object the global
regular functions on its underlying scheme, and the equivalence of sites does not change that
scheme, so the two presheaves of rings are *equal*, not merely isomorphic.  This is what makes
the transport of modules a plain `SheafOfModules.pushforward` along a continuous functor, with
no quasi-coherence hypothesis, no sheafification and no descent input.

`AlgebraicGeometry.Space.ringStructureSheaf` is stated for the topology
`AlgebraicGeometry.Space.SmallEtale.topology` rather than for the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite ...).J`, to which it is definitionally equal:
the projection carries the `Category` instance of the ringed-site structure, and with that
reading instance search no longer finds the continuity of the comparison functor.  This is the
same obstruction that `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`
restates its instances for, and that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean` record.

The additivity of `SheafOfModules.pushforward` is stated for a general continuous functor, but
instance search only reaches it when the sheaf of rings on the source site is syntactically
available: matching the implicit sheaf of rings against a definition such as
`AlgebraicGeometry.Scheme.ringCatSheaf` is beyond the transparency used by instance resolution.
The additivity of each concrete transport below is therefore recorded separately.  For the same
reason the isomorphism class of `SheafOfModules.pullbackObjUnitToUnit` is passed explicitly in
`AlgebraicGeometry.Space.representedAssociatedModuleObjUnitIso`.

Nothing here is an equivalence of categories of *quasi-coherent* modules: whether
`AlgebraicGeometry.SmallEtale.associatedModule` is such an equivalence is Descent,
Proposition 03DX (2), which is not available.  Quasi-coherence is therefore not claimed to be
preserved, and no `stacks` attribute is carried: clause (4) of Stacks 03DU is already carried
by `AlgebraicGeometry.SmallEtale.associatedModule`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]

/-- The pushforward of sheaves of modules along a continuous functor is an additive functor:
on sections it is restriction of scalars along the comparison of the sheaves of rings, which
does not change the addition. -/
instance additive_pushforward (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (SheafOfModules.pushforward.{u} φ).Additive where
  map_add := by intros; ext; rfl

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- Restriction of a sheaf of modules on the small étale site of `T` along the inclusion of the
small Zariski site is additive. -/
instance additive_restrictModule : (restrictModule B T hT).Additive :=
  SheafOfModules.additive_pushforward _

/-- The associated-module functor of the small étale site of `T` is additive, being a left
adjoint between additive categories. -/
instance additive_associatedModule : (associatedModule B T hT).Additive :=
  (associatedModuleAdjunction B T hT).left_adjoint_additive

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Forgetting commutativity preserves the sheaf condition on the small étale site of a
presheaf over `S`: the forgetful functor `CommRingCat ⥤ RingCat` preserves all limits. -/
instance hasSheafCompose_smallEtale_forget₂_ringCat :
    (SmallEtale.topology B S hS F).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  letI : PreservesLimitsOfSize.{u, u + 1} (forget₂ CommRingCat.{u} RingCat.{u}) :=
    preservesLimitsOfSize_forget₂_commRingCat_ringCat
  hasSheafCompose_of_preservesLimitsOfSize _

/-- The structure sheaf of the small étale site of a presheaf over `S`, with commutativity
forgotten: the sheaf of rings `V ↦ Γ(V, 𝒪_V)` in which sheaves of modules on the site are
indexed. -/
noncomputable def ringStructureSheaf : Sheaf (SmallEtale.topology B S hS F) RingCat.{u} :=
  ⟨structurePresheaf B S hS F ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    GrothendieckTopology.HasSheafCompose.isSheaf _ (structurePresheaf_isSheaf' B S hS F)⟩

/-- The underlying presheaf of `ringStructureSheaf` is the structure presheaf composed with the
forgetful functor `CommRingCat ⥤ RingCat`. -/
@[simp]
theorem ringStructureSheaf_obj :
    (ringStructureSheaf B S hS F).obj =
      structurePresheaf B S hS F ⋙ forget₂ CommRingCat.{u} RingCat.{u} :=
  rfl

/-- The sheaf of rings of the small étale ringed site of an algebraic space is the structure
sheaf of its small étale site with commutativity forgotten. -/
theorem ringStructureSheaf_eq_ringSheaf (hF : IsAlgebraicSpace B S hS F) :
    ringStructureSheaf B S hS F =
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  rfl

variable (U : BigFppfOver B S hS)

/-- The small étale topology of the scheme underlying `U` induces, along the equivalence with
the small étale site of `yoneda.obj U`, the small étale topology of `yoneda.obj U`, so the
equivalence is continuous. -/
instance isContinuous_representedSmallEtaleEquivalence_functor :
    (representedSmallEtaleEquivalence B S hS U).functor.IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj U))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
  Functor.le_inducedTopology_iff.1 (representedSmallEtaleEquivalence_topology B S hS U).ge

/-- The inverse of the equivalence between the two small étale sites is continuous as well. -/
instance isContinuous_representedSmallEtaleEquivalence_inverse :
    (representedSmallEtaleEquivalence B S hS U).inverse.IsContinuous
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  Functor.le_inducedTopology_iff.1
    (inducedTopology_symm_of_equivalence (representedSmallEtaleEquivalence B S hS U) _ _
      (representedSmallEtaleEquivalence_topology B S hS U)).ge

/-- **The structure sheaf of the small étale site of `yoneda.obj U` is the structure sheaf of
the small étale site of the scheme underlying `U`, restricted along the equivalence of the two
sites.**  Both sides send an object to the global regular functions on the same scheme, so the
comparison is the identity. -/
noncomputable def representedStructureMap :
    ringStructureSheaf B S hS (yoneda.obj U) ⟶
      ((representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology B S hS (yoneda.obj U))
          (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).obj
        (_root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) where
  hom := 𝟙 _

/-- The underlying morphism of presheaves of `representedStructureMap` is the identity. -/
@[simp]
theorem representedStructureMap_hom :
    (representedStructureMap B S hS U).hom =
      𝟙 (structurePresheaf B S hS (yoneda.obj U) ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  rfl

/-- The comparison of structure sheaves read in the other direction: the structure sheaf of the
small étale site of the scheme underlying `U` is the structure sheaf of the small étale site of
`yoneda.obj U`, restricted along the inverse equivalence. -/
noncomputable def representedStructureMapInverse :
    _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟶
      ((representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
          RingCat.{u}
          (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
          (SmallEtale.topology B S hS (yoneda.obj U))).obj
        (ringStructureSheaf B S hS (yoneda.obj U)) where
  hom := 𝟙 _

/-- **Transport of modules along the equivalence of small étale sites.**  An
`𝒪`-module on the small étale site of the scheme underlying `U` becomes an `𝒪`-module on the
small étale site of the algebraic space `yoneda.obj U`, with the same sections. -/
noncomputable def representedModulePushforward :
    SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⥤
      SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)) :=
  SheafOfModules.pushforward.{u} (representedStructureMap B S hS U)

/-- Transport of modules along the inverse equivalence of small étale sites: an `𝒪`-module on
the small étale site of the algebraic space `yoneda.obj U` becomes an `𝒪`-module on the small
étale site of the scheme underlying `U`. -/
noncomputable def representedModuleRestriction :
    SheafOfModules.{u} (ringStructureSheaf B S hS (yoneda.obj U)) ⥤
      SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :=
  SheafOfModules.pushforward.{u} (representedStructureMapInverse B S hS U)

/-- Transport of modules along the equivalence of small étale sites is additive. -/
instance additive_representedModulePushforward :
    (representedModulePushforward B S hS U).Additive :=
  SheafOfModules.additive_pushforward _

/-- Transport of modules along the inverse equivalence of small étale sites is additive. -/
instance additive_representedModuleRestriction :
    (representedModuleRestriction B S hS U).Additive :=
  SheafOfModules.additive_pushforward _

/-- The sections of a transported module are the sections of the original module at the
corresponding object of the small étale site of the scheme. -/
theorem representedModulePushforward_obj_val_presheaf
    (M : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) :
    ((representedModulePushforward B S hS U).obj M).val.presheaf =
      (representedSmallEtaleEquivalence B S hS U).functor.op ⋙ M.val.presheaf :=
  rfl

/-- Transport along the equivalence of small étale sites carries the structure sheaf of the
scheme underlying `U` to the structure sheaf of the algebraic space `yoneda.obj U`. -/
noncomputable def representedModulePushforwardObjUnitIso :
    (representedModulePushforward B S hS U).obj (SheafOfModules.unit _) ≅
      SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U)) :=
  Iso.refl _

/-- **An `𝒪_T`-module on a scheme `T` underlying an object `U` of the big fppf site over `S`
becomes an `𝒪`-module on the small étale site of the algebraic space `yoneda.obj U`.**  This is
the associated-module functor of Stacks 03DU (4) for the small étale site of `T`, transported
along the equivalence of that site with the small étale site of `yoneda.obj U`. -/
noncomputable def representedAssociatedModule
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules ⥤ Modules.{u, u} B S hS (yoneda.obj U) hF :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    representedModulePushforward B S hS U

/-- The comparison functor to modules on the small étale site of a represented algebraic space
is additive. -/
instance additive_representedAssociatedModule
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    (representedAssociatedModule B S hS U hF).Additive :=
  inferInstanceAs ((_root_.AlgebraicGeometry.SmallEtale.associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
      representedModulePushforward B S hS U).Additive)

/-- **The comparison functor carries the structure sheaf to the structure sheaf.**  The
associated-module functor of the small étale site takes `𝒪_T` to `𝒪`, the small Zariski site
being final in the small étale site, and the transport along the equivalence of sites preserves
the structure sheaf. -/
noncomputable def representedAssociatedModuleObjUnitIso
    (hF : IsAlgebraicSpace B S hS (yoneda.obj U)) :
    (representedAssociatedModule B S hS U hF).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) ≅
      SheafOfModules.unit (ringStructureSheaf B S hS (yoneda.obj U)) :=
  (representedModulePushforward B S hS U).mapIso
      (@asIso _ _ _ _ _ (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) ≪≫
    representedModulePushforwardObjUnitIso B S hS U

end AlgebraicGeometry.Space

end
