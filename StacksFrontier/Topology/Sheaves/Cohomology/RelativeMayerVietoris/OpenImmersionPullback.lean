module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.ShortComplexOfDirectImages
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# Pullback along an open immersion of ringed spaces is exact and preserves injectives

Let `i : U ⟶ X` be an open immersion of ringed spaces. Then `i` factors as an isomorphism of
ringed spaces onto the open subspace cut out by its image, followed by the canonical inclusion of
that open subspace, and pullback along the inclusion is the concrete restriction `(-)|_U` to an
open subset of `X`. Hence pullback of sheaves of modules along `i` preserves injective objects.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.openImmersionImageIso`: the isomorphism of ringed
  spaces from the source of an open immersion onto the open subspace cut out by its image.
* `Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenInclusionIso`: for an open subset
  `U` of `X`, the comparison of the concrete restriction `(-)|_U` with the abstract pullback
  along the canonical inclusion of the open subspace.
* `Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenImmersionIso`: the resulting
  factorisation of `i^*` through the open subspace of the image.
* `Stacks.Cohomology.RelativeMayerVietoris.restrictedPushforwardOpenImmersionIso`: the
  comparison of the restricted direct image along the inclusion of the image of an open
  immersion `i` with `i^* ⋙ (i ≫ f)_*`.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects`: pullback
  along an open immersion preserves injective objects.
* `Stacks.Cohomology.RelativeMayerVietoris.openImmersionImages_cover_intersection`: a cover of
  `X` by the ranges of two open immersions, with a third cutting out their intersection, is a
  cover of `X` by the two images with their meet.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-! ### Pushforward and pullback along an isomorphism -/

/-- Pushforward along an isomorphism of ringed spaces is an equivalence. -/
public theorem modulePushforwardIso_isEquivalence
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    (modulePushforward e.hom).IsEquivalence := by
  have h₁ : modulePushforward (𝟙 X) ≅ modulePushforward e.hom ⋙ modulePushforward e.inv := by
    rw [← e.hom_inv_id]
    exact pushforwardCompIso e.hom e.inv
  have h₂ : modulePushforward (𝟙 Y) ≅ modulePushforward e.inv ⋙ modulePushforward e.hom := by
    rw [← e.inv_hom_id]
    exact pushforwardCompIso e.inv e.hom
  exact .mk' _ ((modulePushforwardId X).symm ≪≫ h₁) (h₂.symm ≪≫ modulePushforwardId Y)

/-- For an isomorphism `e` of ringed spaces, `e^* ⋙ e_*` is isomorphic to the identity. -/
public noncomputable def modulePullbackPushforwardIso_of_iso
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    modulePullback e.hom ⋙ modulePushforward e.hom ≅
      𝟭 (SheafOfModules (structureSheafRing Y)) := by
  have := Stacks.Cohomology.modulePullbackIso_isEquivalence e
  let adj := modulePullbackPushforwardAdjunction e.hom
  have : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful adj
  exact (asIso adj.unit).symm

/-! ### The concrete restriction to an open subset as a pullback -/

/-- Restriction of sheaves of modules to an open subset `U` of `X` is left adjoint to
pushforward along the canonical inclusion of the open subspace. -/
public noncomputable def moduleRestrictionAdjunction
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    moduleRestriction X U ⊣ modulePushforward (X.ofRestrict U.isOpenEmbedding) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := h.isOpenMap.adjunction
  have : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  have : G.IsContinuous
      (Opens.grothendieckTopology (X : TopCat))
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat)) := inferInstance
  let R := structureSheafRing X
  let S := structureSheafRing (X.restrict U.isOpenEmbedding)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj S := structureSheafHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components V.unop]
    exact CategoryTheory.Functor.map_id_apply R.obj (Opposite.op (F.obj V.unop)) x
  change SheafOfModules.pushforward φ ⊣ SheafOfModules.pushforward ψ
  exact SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- Restriction to an open subset is isomorphic to the pullback along the canonical inclusion
of the corresponding open subspace. -/
public noncomputable def modulePullbackOpenInclusionIso
    (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    moduleRestriction X U ≅ modulePullback (X.ofRestrict U.isOpenEmbedding) :=
  (moduleRestrictionAdjunction X U).leftAdjointUniq
    (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))

/-- Pullback along the canonical inclusion of an open subspace preserves injective objects. -/
public theorem modulePullbackOpenInclusion_preservesInjective
    (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (I : SheafOfModules (structureSheafRing X)) [Injective I] :
    Injective ((modulePullback (X.ofRestrict U.isOpenEmbedding)).obj I) :=
  Injective.of_iso ((modulePullbackOpenInclusionIso X U).app I)
    ((moduleRestriction_preservesInjectiveObjects X U).injective_obj inferInstance)

/-! ### Reducing an abstract open immersion to the inclusion of its image -/

/-- An open immersion of ringed spaces is an isomorphism onto the open subspace cut out by
its image. -/
public noncomputable def openImmersionImageIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    U ≅ restrictToOpen X (immImage i) := by
  let j := openSubspaceInclusion X (immImage i)
  have : SheafedSpace.IsOpenImmersion j :=
    SheafedSpace.IsOpenImmersion.ofRestrict X (immImage i).isOpenEmbedding
  have hrange : Set.range i.hom.base = Set.range j.hom.base := calc
    _ = (immImage i : Set X.carrier) := rfl
    _ = Set.range (ConcreteCategory.hom (Opens.inclusion' (immImage i))) :=
      (Opens.set_range_inclusion' (immImage i)).symm
    _ = Set.range j.hom.base := rfl
  exact SheafedSpace.isoMk
    (PresheafedSpace.IsOpenImmersion.isoOfRangeEq i.hom j.hom hrange)

/-- The open immersion `i` is `openImmersionImageIso i` followed by the inclusion of the open
subspace cut out by its image. -/
public theorem openImmersionImageIso_hom_comp
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (openImmersionImageIso i).hom ≫ openSubspaceInclusion X (immImage i) = i := by
  let j := openSubspaceInclusion X (immImage i)
  have : SheafedSpace.IsOpenImmersion j :=
    SheafedSpace.IsOpenImmersion.ofRestrict X (immImage i).isOpenEmbedding
  have hrange : Set.range i.hom.base = Set.range j.hom.base := calc
    _ = (immImage i : Set X.carrier) := rfl
    _ = Set.range (ConcreteCategory.hom (Opens.inclusion' (immImage i))) :=
      (Opens.set_range_inclusion' (immImage i)).symm
    _ = Set.range j.hom.base := rfl
  dsimp [openImmersionImageIso]
  exact SheafedSpace.forgetToPresheafedSpace_faithful.map_injective
    (PresheafedSpace.IsOpenImmersion.lift_fac j.hom i.hom (by simp [hrange]))

/-- The pullback along an open immersion is the pullback along the inclusion of its image
followed by the pullback along `openImmersionImageIso`. -/
public noncomputable def modulePullbackOpenImmersionIso
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    modulePullback i ≅
      modulePullback (openSubspaceInclusion X (immImage i)) ⋙
        modulePullback (openImmersionImageIso i).hom :=
  (eqToIso (congrArg (fun k : U ⟶ X => modulePullback k)
      (openImmersionImageIso_hom_comp i).symm)).trans
    (pullbackCompIso (openImmersionImageIso i).hom (openSubspaceInclusion X (immImage i)))

/-- Pullback along an open immersion preserves injective objects. -/
public theorem modulePullback_preservesInjectiveObjects
    {X U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] :
    (modulePullback i).PreservesInjectiveObjects := by
  constructor
  intro I _
  have := Stacks.Cohomology.modulePullbackIso_isEquivalence (openImmersionImageIso i)
  have : (modulePullback (openImmersionImageIso i).hom).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_isEquivalence
  exact (Injective.iso_iff ((modulePullbackOpenImmersionIso i).app I)).2 <|
    (modulePullback (openImmersionImageIso i).hom).injective_obj_of_injective
      (modulePullbackOpenInclusion_preservesInjective X (immImage i) I)

/-- Restriction to an open subset `U` of `X`, followed by pushforward along the inclusion of
the open subspace and then along `f`, is the pullback-pushforward composite attached to the
inclusion. -/
public noncomputable def restrictedPushforwardIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens X.carrier) :
    (moduleRestriction X U ⋙
        modulePushforward (X.ofRestrict U.isOpenEmbedding)) ⋙ modulePushforward f ≅
      modulePullback (X.ofRestrict U.isOpenEmbedding) ⋙
        modulePushforward (X.ofRestrict U.isOpenEmbedding ≫ f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleRestriction X U)
      (pushforwardCompIso (X.ofRestrict U.isOpenEmbedding) f).symm ≪≫
    Functor.isoWhiskerRight (modulePullbackOpenInclusionIso X U)
      (modulePushforward (X.ofRestrict U.isOpenEmbedding ≫ f))

/-- The restricted direct image attached to the image of an open immersion `i` is isomorphic to
the one attached to `i` itself. -/
public noncomputable def restrictedPushforwardOpenImmersionIso
    {X Y U : RingedSpace.{u, u}} (i : U ⟶ X) [SheafedSpace.IsOpenImmersion i] (f : X ⟶ Y) :
    modulePullback (openSubspaceInclusion X (immImage i)) ⋙
        modulePushforward (openSubspaceInclusion X (immImage i) ≫ f) ≅
      modulePullback i ⋙ modulePushforward (i ≫ f) := by
  let e := openImmersionImageIso i
  let j := openSubspaceInclusion X (immImage i)
  have : SheafedSpace.IsOpenImmersion j :=
    SheafedSpace.IsOpenImmersion.ofRestrict X (immImage i).isOpenEmbedding
  have he : e.hom ≫ j = i := openImmersionImageIso_hom_comp i
  have hipush : i ≫ f = e.hom ≫ (j ≫ f) := by rw [← Category.assoc, he]
  have epullback : modulePullback i ≅ modulePullback j ⋙ modulePullback e.hom :=
    (eqToIso (congrArg (fun k : U ⟶ X => modulePullback k) he.symm)).trans
      (pullbackCompIso e.hom j)
  have epushforward : modulePushforward (i ≫ f) ≅
      modulePushforward e.hom ⋙ modulePushforward (j ≫ f) :=
    (eqToIso (congrArg modulePushforward hipush)).trans
      (pushforwardCompIso e.hom (j ≫ f))
  let ecancel := modulePullbackPushforwardIso_of_iso e
  let eAssoc₁ := Functor.associator (modulePullback j) (modulePullback e.hom)
    (modulePushforward e.hom ⋙ modulePushforward (j ≫ f))
  let eAssoc₂ := Functor.isoWhiskerLeft (modulePullback j)
    (Functor.associator (modulePullback e.hom) (modulePushforward e.hom)
      (modulePushforward (j ≫ f))).symm
  let eCancel := Functor.isoWhiskerLeft (modulePullback j)
    (Functor.isoWhiskerRight ecancel (modulePushforward (j ≫ f)))
  let eUnit := Functor.isoWhiskerLeft (modulePullback j)
    (Functor.leftUnitor (modulePushforward (j ≫ f)))
  exact eUnit.symm ≪≫ eCancel.symm ≪≫ eAssoc₂ ≪≫ eAssoc₁.symm ≪≫
    (Functor.isoWhiskerRight epullback
      (modulePushforward e.hom ⋙ modulePushforward (j ≫ f))).symm ≪≫
    Functor.isoWhiskerLeft (modulePullback i) epushforward.symm

/-- A cover of `X` by the ranges of two open immersions, with a third cutting out their
intersection, is a cover of `X` by the two images with their meet. -/
public theorem openImmersionImages_cover_intersection
    {X U V W : RingedSpace.{u, u}} (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
    [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
    [SheafedSpace.IsOpenImmersion iW]
    (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
    (intersection : Set.range iW.hom.base =
      Set.range iU.hom.base ∩ Set.range iV.hom.base) :
    immImage iU ⊔ immImage iV = ⊤ ∧
      immImage iW = immImage iU ⊓ immImage iV := by
  constructor
  · ext x
    show x ∈ Set.range iU.hom.base ∪ Set.range iV.hom.base ↔ x ∈ Set.univ
    simpa using congrArg (fun s : Set X.carrier => x ∈ s) cover
  · ext x
    show x ∈ Set.range iW.hom.base ↔
      x ∈ Set.range iU.hom.base ∩ Set.range iV.hom.base
    simpa using congrArg (fun s : Set X.carrier => x ∈ s) intersection

end Stacks.Cohomology.RelativeMayerVietoris

end
