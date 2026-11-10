module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence

/-!
# The localization of a ringed topos depends on the sheaf only up to isomorphism

Let `X` be a ringed topos presented by a site `(C, J)` and let `e : F ≅ F'` be an isomorphism of
sheaves of sets on `C`. The localization of `X` at `F` is carried along `e` to the localization
of `X` at `F'`.

## Main definitions

* `AlgebraicGeometry.RingedTopos.elementSiteMapIso`: the site of elements of `F` as the site of
  elements of `F'`, for `F ≅ F'`, as a functor of sites over the site of `X`.
* `AlgebraicGeometry.RingedTopos.localizedToposEquivalenceOfIso` and
  `AlgebraicGeometry.RingedTopos.localizedRingedToposHomOfIso`: the localization depends on the
  sheaf only up to isomorphism, on the topoi and as a morphism of ringed topoi.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{v, u, v}) [EssentiallySmall.{v} X.C]

/-! ### Moving a localization along an isomorphism of sheaves -/

section OfIso

variable {F F' : X.Topos} (e : F ≅ F')

/-- **The site of elements of `F` is the site of elements of `F'`, for `F ≅ F'`.** An object of
the site of elements is a pair `(U, s)` with `s : yoneda.obj U ⟶ F.obj`, and post-composing with
the isomorphism is an equivalence onto the site of elements of `F'`. It is a functor over the
site of `X` (`elementSiteMapIso_comp_elementProjection`). -/
abbrev elementSiteMapIso : elementSite X F ⥤ elementSite X F' :=
  (CostructuredArrow.mapIso ((sheafToPresheaf X.J (Type v)).mapIso e)).functor

/-- `elementSiteMapIso X e` is an equivalence of categories. -/
instance : (elementSiteMapIso X e).IsEquivalence :=
  (CostructuredArrow.mapIso ((sheafToPresheaf X.J (Type v)).mapIso e)).isEquivalence_functor

omit [EssentiallySmall.{v} X.C] in
/-- **Post-composition with the isomorphism leaves the projection to the site of `X`
untouched**: it changes the section, not the object it is a section over. -/
theorem elementSiteMapIso_comp_elementProjection :
    elementSiteMapIso X e ⋙ elementProjection X F' = elementProjection X F :=
  rfl

omit [EssentiallySmall.{v} X.C] in
/-- **The topologies of Stacks 0791 correspond along `elementSiteMapIso`.** A sieve `T` on `Y` is
covering for the site of elements of `F` exactly when its image under `elementSiteMapIso X e` is
covering for the site of elements of `F'`. -/
theorem functorPushforward_mem_elementTopology_mapIso_iff (Y : elementSite X F) (T : Sieve Y) :
    Sieve.functorPushforward (elementSiteMapIso X e) T ∈
        elementTopology X F' ((elementSiteMapIso X e).obj Y) ↔ T ∈ elementTopology X F Y := by
  simp only [elementTopology, elementProjection]
  rw [Stacks.Topos.Localized.restrictedTopology_eq_topology,
    Stacks.Topos.Localized.restrictedTopology_eq_topology,
    Stacks.Topos.Localized.mem_topology_iff, Stacks.Topos.Localized.mem_topology_iff,
    ← Sieve.functorPushforward_comp]
  rfl

/-- The two sites of elements are dense subsites of one another, being equivalent compatibly
with their topologies. -/
instance elementSiteMapIso_isDenseSubsite : (elementSiteMapIso X e).IsDenseSubsite
    (elementTopology X F) (elementTopology X F') where
  functorPushforward_mem_iff := functorPushforward_mem_elementTopology_mapIso_iff X e _ _

omit [EssentiallySmall.{v} X.C] in
/-- Every category `A` has limits indexed by the categories of structured arrows of
`(elementSiteMapIso X e).op`, which have initial objects. -/
theorem hasLimitsOfShape_structuredArrow_elementSiteMapIso (A : Type*) [Category A]
    (T : (elementSite X F')ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow T (elementSiteMapIso X e).op) A :=
  have := (mkInitialOfLeftAdjoint (elementSiteMapIso X e).op
    (elementSiteMapIso X e).asEquivalence.op.symm.toAdjunction T).hasInitial
  ⟨fun _ => inferInstance⟩

/-- **The localization of a ringed topos at a sheaf depends on the sheaf only up to
isomorphism**, on the underlying topoi: an isomorphism `F ≅ F'` of sheaves of sets carries the
topos of the localization at `F` to the topos of the localization at `F'`.

It is given by restriction along `elementSiteMapIso`, a functor of sites over the site of `X`.
It moves a localization from one spelling of a sheaf to an isomorphic one, as from an inverse
image to a representable sheaf in the Zariski gluing of Stacks 04I7. -/
noncomputable def localizedToposEquivalenceOfIso :
    (localizedRingedTopos X F).Topos ≌ (localizedRingedTopos X F').Topos :=
  have := hasLimitsOfShape_structuredArrow_elementSiteMapIso X e (Type v)
  Functor.IsDenseSubsite.sheafEquiv (elementTopology X F) (elementTopology X F')
    (elementSiteMapIso X e) (Type v)

/-- `elementSiteMapIso` is continuous for the topology `(localizedRingedTopos X F').J`, which is
definitionally `elementTopology X F'` but has different discrimination-tree keys. -/
instance isContinuous_elementSiteMapIso_localized :
    Functor.IsContinuous (elementSiteMapIso X e)
      (elementTopology X F) (localizedRingedTopos X F').J :=
  inferInstanceAs (Functor.IsContinuous (elementSiteMapIso X e)
    (elementTopology X F) (elementTopology X F'))

/-- The identification of the two localized topoi, read as a morphism of topoi, with restriction
along `elementSiteMapIso` as its inverse image. -/
noncomputable def localizedToposMorphismOfIso :
    MorphismOfTopoi (localizedRingedTopos X F).Topos (localizedRingedTopos X F').Topos where
  inverseImage := (localizedToposEquivalenceOfIso X e).inverse
  pushforward := (localizedToposEquivalenceOfIso X e).functor
  adj := (localizedToposEquivalenceOfIso X e).symm.toAdjunction
  preservesFiniteLimits :=
    haveI := (localizedToposEquivalenceOfIso X e).symm.toAdjunction.rightAdjoint_preservesLimits
    ⟨fun _ _ _ ↦ inferInstance⟩

omit [EssentiallySmall.{v} X.C] in
/-- **The two localized structure sheaves correspond.** The structure sheaf of the localization
at `F'`, restricted along `elementSiteMapIso`, *is* the structure sheaf of the localization at
`F`: both are the restriction of `O` along the projection from a site of elements. -/
theorem sheafPushforward_localizedRingedTopos_O_mapIso :
    ((elementSiteMapIso X e).sheafPushforwardContinuous CommRingCat.{v}
        (elementTopology X F) (localizedRingedTopos X F').J).obj
      (localizedRingedTopos X F').O = (localizedRingedTopos X F).O :=
  rfl

/-- The comparison of the two localized structure sheaves in inverse-image form, which is the
equality above read through `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`. -/
noncomputable def localizedStructureSheafIsoOfIso :
    (inverseImageCommRingFunctor (localizedToposMorphismOfIso X e)).obj
        (localizedRingedTopos X F').O ≅ (localizedRingedTopos X F).O :=
  restrictionCommRingIso (elementTopology X F) (localizedRingedTopos X F').J
    (elementSiteMapIso X e) (localizedRingedTopos X F').O

/-- **The localization of a ringed topos at a sheaf depends on the sheaf only up to isomorphism,
as a morphism of ringed topoi** — structure sheaves included. Its morphism of topoi is
`localizedToposMorphismOfIso`, an equivalence, and its structure map is the adjunct of
`localizedStructureSheafIsoOfIso`, so it is an isomorphism. -/
noncomputable def localizedRingedToposHomOfIso :
    RingedToposHom (localizedRingedTopos X F) (localizedRingedTopos X F') where
  toToposHom := localizedToposMorphismOfIso X e
  fSharp := (commRingImageAdjunction (localizedToposMorphismOfIso X e)).homEquiv _ _
    (localizedStructureSheafIsoOfIso X e).hom

end OfIso

end AlgebraicGeometry.RingedTopos

end
