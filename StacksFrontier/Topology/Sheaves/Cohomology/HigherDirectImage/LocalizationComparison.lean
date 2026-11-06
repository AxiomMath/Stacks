module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Restriction

/-!
# Localization of higher direct images: the comparison before deriving

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `V ⊆ Y` be open, with
inverse image `U = f⁻¹(V) ⊆ X`.  Restricting `f` gives a morphism of ringed spaces
`f|_U : (U, 𝒪_X|_U) ⟶ (V, 𝒪_Y|_V)`, and Stacks 01E5 asserts that higher direct images commute
with restriction to `V`, as do the total right derived pushforwards of bounded below complexes.

This file builds the undeived half of that statement and the exactness input it needs.  The
comparison `(f|_U)_* (ℱ|_U) = (f_* ℱ)|_V` *before* deriving is constructed and characterized:
on sections over an open `W ⊆ V` both sides are `ℱ(f⁻¹ W)`, and the comparison is the identity
there.  Restriction to an open is shown to be exact, so its right derived functor on bounded
below derived categories *is* ordinary termwise restriction; and restriction to `V` is carried
through the ordinary right derived functors of `f_*`.

The two displayed isomorphisms of Stacks 01E5 are **not** proved here; see the implementation
notes for exactly what is missing.

## Main definitions

* `restrictToOpen` is the open subspace `(U, 𝒪_X|_U)` of a ringed space, reproduced as a
  reducible definition.
* `preimageOpen` is the inverse image of an open under a morphism of ringed spaces.
* `openSubspaceInclusion` is the canonical open immersion of an open subspace.
* `moduleRestriction` is ordinary restriction of sheaves of modules to an open subspace.
* `restrictedMorphismBase`, `restrictedMorphismSheafHom` and `restrictedMorphism` are the
  restriction `f|_{f⁻¹(V)} : f⁻¹(V) ⟶ V` of a morphism of ringed spaces over an open of its
  target, given explicitly by its continuous map and its map of structure sheaves.
* `restrictOpensIso` is the identification `f⁻¹(W) = (f|_U)⁻¹(W)` of opens of `X`, for `W ⊆ V`.
* `modulePushforwardRestrictIso` is the canonical comparison before deriving.
* `moduleRestrictionDerivedTermwiseIso` and `moduleRestrictionDerivedCochainIso` identify the
  right derived functor of restriction with ordinary termwise restriction.

## Main results

* `restrictedMorphism_comp_openSubspaceInclusion`: the restricted morphism really is `f`,
  namely `j_U ≫ f = f|_U ≫ j_V`.
* `moduleRestriction_isRightAdjoint`, `moduleRestriction_isLeftAdjoint`,
  `moduleRestriction_additive` and `moduleRestriction_preservesHomology`: restriction to an
  open subspace is additive and exact, being both a left and a right adjoint.
* `modulePushforwardRestrictIso_hom_app_val_app` and
  `modulePushforwardRestrictIso_hom_app_val_app_heq`: the comparison before deriving is the
  identity on sections, which pins it down and rules out multiplication by an automorphism.
* `isIso_rightDerivedFunctorPlusUnit`: the bounded below right derived functor of an exact
  additive functor is the functor itself; its derived-functor unit is an isomorphism.
* `moduleRestrictionRightDerivedFunctorPlusUnit_isIso`: the instance of that for restriction,
  so that no derived pullback is needed to describe derived restriction.
* `rightDerivedPushforwardRestrictIso`: restricting the `p`-th right derived functor of `f_*`
  computes the `p`-th right derived functor of the composite `ℱ ↦ (f|_U)_*(ℱ|_U)`.

## Implementation notes

Ordinary restriction is `restMod`, with the structure sheaves identified definitionally; the
open subspace and `asRingSheafedSpace` are reducible so that typeclass inference can see the
subspace topology, which every sheaf-pushforward instance below takes as an argument.

`restrictedMorphism` is built by hand rather than through
`PresheafedSpace.IsOpenImmersion.lift`, because the comparison
`modulePushforwardRestrictIso` needs its continuous map and its map of structure sheaves
explicitly: both composites in question are `SheafOfModules.pushforward` along the two
composite functors `Opens V ⥤ Opens X`, these two functors agree objectwise by
`isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase`, and the comparison is the induced
`SheafOfModules.pushforwardCongr₂`.

What is **not** here is Stacks 01E5 itself: `higherDirectImageRestrictIso`, saying that
`moduleRestriction X U ⋙ (modulePushforward (f|_U)).rightDerived p` agrees with
`(modulePushforward f).rightDerived p ⋙ moduleRestriction Y V`, and its bounded below derived
analogue.  `rightDerivedPushforwardRestrictIso` gives one half: since restriction to `V` is
exact, it passes through right derived functors, so the right-hand side computes the right
derived functors of the *composite* `moduleRestriction X U ⋙ modulePushforward (f|_U)`.
Identifying those with `moduleRestriction X U ⋙ (modulePushforward (f|_U)).rightDerived p`
requires restriction to send injective sheaves of modules to injective sheaves of modules —
Stacks 01E1 — which is not available: it would follow from
`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` applied to
`jShriekAdjunction` once extension by zero `jShriek00A7` is known to preserve monomorphisms,
and `SheafOfModules.pullback` is defined as an abstract left adjoint, with no description from
which that exactness could be read off.  Everything in this file is independent of that gap.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The open subspace `(U, 𝒪_X|_U)` of a ringed space `(X, 𝒪_X)` cut out by an open `U ⊆ X`:
the carrier is `U` with its subspace topology, and the structure sheaf is the restriction of
`𝒪_X` along the open embedding of `U`.  This is `openSubspace` of Stacks 00A1 (3), whose sheaf
condition is reused, written out as a reducible definition: the carrier must reduce to the
subspace `(Opens.toTopCat X).obj U` at reducible transparency, since that subspace carries the
Grothendieck topology which is an argument of every sheaf-pushforward instance below. -/
@[reducible] noncomputable def restrictToOpen (X : RingedSpace.{u, u}) (U : Opens X) :
    RingedSpace.{u, u} :=
  SheafedSpace.mk
    (PresheafedSpace.mk ((Opens.toTopCat (X : TopCat)).obj U)
      (U.isOpenEmbedding.functor.op ⋙ X.presheaf))
    (openSubspace X U).IsSheaf

/-- The inverse image of an open subset under the underlying continuous map of a morphism of
ringed spaces. -/
noncomputable abbrev preimageOpen {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y) :
    Opens X :=
  (Opens.map f.hom.base).obj V

/-- The canonical open immersion from an open subspace into the ambient ringed space. -/
noncomputable abbrev openSubspaceInclusion (X : RingedSpace.{u, u}) (U : Opens X) :
    restrictToOpen X U ⟶ X :=
  X.ofRestrict U.isOpenEmbedding

/-- A ringed space with commutativity forgotten from its structure sheaf, so that the abstract
`SheafOfModules` API over `RingCat` applies to it.  Reducible for the same reason as
`restrictToOpen`. -/
@[reducible] noncomputable def asRingSheafedSpace (X : RingedSpace.{u, u}) :
    SheafedSpace RingCat.{u} :=
  SheafedSpace.mk (PresheafedSpace.mk X.carrier (structureSheafRing X).obj)
    (structureSheafRing X).property

/-- Ordinary restriction of sheaves of modules to an open subspace.  On underlying presheaves
this is precomposition with the inclusion of the poset of opens, so that the sections of
`ℱ|_U` over an open `W ⊆ U` are the sections of `ℱ` over `W`; the structure sheaf of the open
subspace is the restriction of `𝒪_X` definitionally, so no change of rings occurs. -/
noncomputable def moduleRestriction (X : RingedSpace.{u, u}) (U : Opens X) :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (restrictToOpen X U)) :=
  restMod (asRingSheafedSpace X) U

section Restricted

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- The continuous map underlying the restriction `f|_{f⁻¹(V)} : f⁻¹(V) ⟶ V` of a morphism of
ringed spaces: it sends a point `x ∈ f⁻¹(V)` to `f(x)`, viewed as a point of `V`. -/
noncomputable def restrictedMorphismBase :
    (Opens.toTopCat (X : TopCat)).obj (preimageOpen f V) ⟶
      (Opens.toTopCat (Y : TopCat)).obj V :=
  TopCat.ofHom ⟨fun x => ⟨f.hom.base x.1, x.2⟩,
    Continuous.subtype_mk (f.hom.base.hom.continuous.comp continuous_subtype_val) _⟩

/-- On points, the restriction of `f` followed by the inclusion of `V` is the inclusion of
`f⁻¹(V)` followed by `f`.  Both sides send `x` to `f(x)`, so this holds by definition. -/
theorem restrictedMorphismBase_comp_inclusion :
    restrictedMorphismBase f V ≫ Opens.inclusion' V =
      Opens.inclusion' (preimageOpen f V) ≫ f.hom.base :=
  rfl

/-- The image in `Y` of an open of the subspace `V` is contained in `V`. -/
theorem isOpenEmbeddingFunctor_obj_le (W : Opens ((Opens.toTopCat (Y : TopCat)).obj V)) :
    V.isOpenEmbedding.functor.obj W ≤ V := by
  rintro z ⟨y, -, rfl⟩
  exact y.2

/-- For an open `W ⊆ V`, the inverse image of `W` under the restricted morphism, viewed as an
open of `X`, is the inverse image under `f` of `W` viewed as an open of `Y`.  This is the
identification of opens along which the two composites of pushforward functors agree. -/
theorem isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase
    (W : Opens ((Opens.toTopCat (Y : TopCat)).obj V)) :
    (preimageOpen f V).isOpenEmbedding.functor.obj
        ((Opens.map (restrictedMorphismBase f V)).obj W) =
      (Opens.map f.hom.base).obj (V.isOpenEmbedding.functor.obj W) := by
  have hmap : (Opens.map (Opens.inclusion' (preimageOpen f V))).obj
      ((Opens.map f.hom.base).obj (V.isOpenEmbedding.functor.obj W)) =
        (Opens.map (restrictedMorphismBase f V)).obj W :=
    congrArg (Opens.map (restrictedMorphismBase f V)).obj (Opens.map_functor_eq W)
  rw [← hmap, Opens.functor_map_eq_inf, inf_eq_left]
  exact fun z hz => isOpenEmbeddingFunctor_obj_le V W hz

/-- The map of structure sheaves underlying the restriction `f|_{f⁻¹(V)}`: over an open
`W ⊆ V` it is the component `f^♯ : 𝒪_Y(W) ⟶ 𝒪_X(f⁻¹ W)` of `f`, followed by the identification
of `f⁻¹(W)` with the inverse image of `W` inside the subspace `f⁻¹(V)`. -/
noncomputable def restrictedMorphismSheafHom :
    (V.isOpenEmbedding.functor.op ⋙ Y.presheaf) ⟶
      (Opens.map (restrictedMorphismBase f V)).op ⋙
        ((preimageOpen f V).isOpenEmbedding.functor.op ⋙ X.presheaf) where
  app W := f.hom.c.app (op (V.isOpenEmbedding.functor.obj W.unop)) ≫
    X.presheaf.map
      (eqToHom (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W.unop)).op
  naturality W₁ W₂ i := by
    dsimp
    rw [← Category.assoc, f.hom.c.naturality, Category.assoc, Category.assoc]
    congr 1
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))

/-- The components of `restrictedMorphismSheafHom`, by definition. -/
theorem restrictedMorphismSheafHom_app
    (W : (Opens ((Opens.toTopCat (Y : TopCat)).obj V))ᵒᵖ) :
    (restrictedMorphismSheafHom f V).app W =
      f.hom.c.app (op (V.isOpenEmbedding.functor.obj W.unop)) ≫
        X.presheaf.map
          (eqToHom (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W.unop)).op :=
  rfl

/-- The restriction `f|_{f⁻¹(V)} : f⁻¹(V) ⟶ V` of a morphism of ringed spaces to an open
subspace of its target, assembled from `restrictedMorphismBase` and
`restrictedMorphismSheafHom`. -/
noncomputable def restrictedMorphism :
    restrictToOpen X (preimageOpen f V) ⟶ restrictToOpen Y V :=
  InducedCategory.homMk
    { base := restrictedMorphismBase f V
      c := restrictedMorphismSheafHom f V }

/-- The continuous map underlying the restricted morphism, by definition. -/
theorem restrictedMorphism_hom_base :
    (restrictedMorphism f V).hom.base = restrictedMorphismBase f V :=
  rfl

/-- The map of structure sheaves underlying the restricted morphism, by definition. -/
theorem restrictedMorphism_hom_c :
    (restrictedMorphism f V).hom.c = restrictedMorphismSheafHom f V :=
  rfl

/-- The restricted morphism followed by the open immersion of `V` is the open immersion of
`f⁻¹(V)` followed by `f`: the restricted morphism really is `f` restricted. -/
theorem restrictedMorphism_comp_openSubspaceInclusion :
    openSubspaceInclusion X (preimageOpen f V) ≫ f =
      restrictedMorphism f V ≫ openSubspaceInclusion Y V := by
  apply InducedCategory.hom_ext
  show (openSubspaceInclusion X (preimageOpen f V)).hom ≫ f.hom =
    (restrictedMorphism f V).hom ≫ (openSubspaceInclusion Y V).hom
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq (NatTrans.ext (funext fun W₀ => ?_)))
  show f.hom.c.app W₀ ≫ X.presheaf.map
        ((preimageOpen f V).isOpenEmbedding.isOpenMap.adjunction.counit.app
          ((Opens.map f.hom.base).obj W₀.unop)).op =
      Y.presheaf.map (V.isOpenEmbedding.isOpenMap.adjunction.counit.app W₀.unop).op ≫
        f.hom.c.app (op (V.isOpenEmbedding.functor.obj
            ((Opens.map (Opens.inclusion' V)).obj W₀.unop))) ≫
          X.presheaf.map (eqToHom
            (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V _)).op
  refine Eq.trans ?_ (f.hom.c.naturality_assoc _ _).symm
  congr 1
  exact ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))

end Restricted

section Instances

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pushforward functor on sheaves of modules is a right adjoint. -/
noncomputable instance modulePushforward_isRightAdjoint_instance :
    (modulePushforward f).IsRightAdjoint :=
  modulePushforward_isRightAdjoint f

end Instances

section RestrictionInstances

variable (X : RingedSpace.{u, u}) (U : Opens X)

/-- Restriction to an open subspace is a right adjoint: it is the right adjoint of extension
by zero, by Stacks 00A7 (2). -/
noncomputable instance moduleRestriction_isRightAdjoint :
    (moduleRestriction X U).IsRightAdjoint :=
  (jShriekAdjunction (asRingSheafedSpace X) U).isRightAdjoint

/-- Restriction to an open subspace is additive, being a right adjoint. -/
noncomputable instance moduleRestriction_additive : (moduleRestriction X U).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction to an open subspace is also a *left* adjoint, namely the left adjoint of
pushforward along the open immersion.  The input is that the open-image functor
`Opens U ⥤ Opens X` is cocontinuous — equivalently that `Opens.map` of the inclusion is
cover-preserving — and is itself a left adjoint, while the comparison of structure sheaves is
the identity. -/
theorem moduleRestriction_isLeftAdjoint : (moduleRestriction X U).IsLeftAdjoint := by
  have h1 : (jFun (asRingSheafedSpace X) U).IsCocontinuous
      (Opens.grothendieckTopology _) (Opens.grothendieckTopology _) :=
    (IsOpenMap.adjunction U.isOpenEmbedding.isOpenMap).isCocontinuous_iff_coverPreserving _ _
      |>.mpr (coverPreserving_opens_map _)
  have h2 : (jFun (asRingSheafedSpace X) U).IsLeftAdjoint :=
    (IsOpenMap.adjunction U.isOpenEmbedding.isOpenMap).isLeftAdjoint
  have h3 : IsIso (phiSh (asRingSheafedSpace X) U) := by
    rw [show phiSh (asRingSheafedSpace X) U = 𝟙 _ from rfl]; exact IsIso.id _
  exact SheafOfModules.isLeftAdjoint_pushforward_of_isIso (phiSh (asRingSheafedSpace X) U)

/-- Restriction to an open subspace is exact, and hence preserves homology: it preserves
finite limits because it is a right adjoint and finite colimits because it is a left
adjoint. -/
theorem moduleRestriction_preservesHomology : (moduleRestriction X U).PreservesHomology := by
  have h4 := moduleRestriction_isLeftAdjoint X U
  have : PreservesFiniteColimits (moduleRestriction X U) := inferInstance
  have : PreservesFiniteLimits (moduleRestriction X U) := inferInstance
  exact Functor.preservesHomologyOfExact _

attribute [instance] moduleRestriction_preservesHomology

end RestrictionInstances

section Comparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- The two ways of reading an open `W ⊆ V` as an open of `X` agree: taking the inverse image
under the restricted morphism and then including into `X` is taking the image in `Y` and then
the inverse image under `f`.  Since `Opens X` is a poset, naturality is automatic. -/
noncomputable def restrictOpensIso :
    jFun (asRingSheafedSpace Y) V ⋙ opensMap f ≅
      opensMap (restrictedMorphism f V) ⋙ jFun (asRingSheafedSpace X) (preimageOpen f V) :=
  NatIso.ofComponents
    (fun W =>
      eqToIso (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W).symm)
    (fun _ => Subsingleton.elim _ _)

/-- The two composites of structure-sheaf comparisons agree along `restrictOpensIso`.  This is
the hypothesis of `SheafOfModules.pushforwardCongr₂` which produces
`modulePushforwardRestrictIso`: over an open `W ⊆ V` both sides are the component
`f^♯ : 𝒪_Y(W) ⟶ 𝒪_X(f⁻¹ W)` of `f`, because the comparisons of the structure sheaves of the
two open subspaces are identities and the two identifications of `f⁻¹(W)` are inverse. -/
theorem structureSheafHom_restrictedMorphism_compatible :
    (structureSheafHom (restrictedMorphism f V) ≫
        ((opensMap (restrictedMorphism f V)).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).map
          (phiSh (asRingSheafedSpace X) (preimageOpen f V))) ≫
      (Functor.sheafPushforwardContinuousNatTrans (restrictOpensIso f V).hom RingCat.{u}
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).app (structureSheafRing X) =
    phiSh (asRingSheafedSpace Y) V ≫
      ((jFun (asRingSheafedSpace Y) V).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).map
        (structureSheafHom f) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_))
  have key : (restrictedMorphismSheafHom f V).app W ≫
      X.presheaf.map ((restrictOpensIso f V).hom.app W.unop).op =
      f.hom.c.app (op (V.isOpenEmbedding.functor.obj W.unop)) := by
    have h2 : X.presheaf.map
          (eqToHom (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W.unop)).op ≫
        X.presheaf.map ((restrictOpensIso f V).hom.app W.unop).op = 𝟙 _ :=
      (X.presheaf.map_comp _ _).symm.trans (X.presheaf.map_id _)
    rw [restrictedMorphismSheafHom_app, Category.assoc, h2]
    exact Category.comp_id _
  show ((forget₂ CommRingCat.{u} RingCat.{u}).map ((restrictedMorphismSheafHom f V).app W) ≫
        𝟙 _) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (X.presheaf.map ((restrictOpensIso f V).hom.app W.unop).op) =
    𝟙 _ ≫ (forget₂ CommRingCat.{u} RingCat.{u}).map
      (f.hom.c.app (op (V.isOpenEmbedding.functor.obj W.unop)))
  rw [Category.comp_id, Category.id_comp, ← Functor.map_comp, key]
  rfl

/-- **Before deriving, pushforward commutes with ordinary restriction.**  Restricting a sheaf
of `𝒪_X`-modules to `f⁻¹(V)` and pushing forward along `f|_{f⁻¹(V)}` agrees with pushing
forward along `f` and restricting to `V`, naturally in the sheaf of modules.  Both composites
are pushforwards along the two composite functors `Opens V ⥤ Opens X` identified by
`restrictOpensIso`, and this is the induced comparison; it is the identity on sections. -/
noncomputable def modulePushforwardRestrictIso :
    moduleRestriction X (preimageOpen f V) ⋙ modulePushforward (restrictedMorphism f V) ≅
      modulePushforward f ⋙ moduleRestriction Y V :=
  SheafOfModules.pushforwardComp (structureSheafHom (restrictedMorphism f V))
      (phiSh (asRingSheafedSpace X) (preimageOpen f V)) ≪≫
    SheafOfModules.pushforwardCongr₂ _ (restrictOpensIso f V)
      (structureSheafHom_restrictedMorphism_compatible f V) ≪≫
    (SheafOfModules.pushforwardComp (phiSh (asRingSheafedSpace Y) V)
      (structureSheafHom f)).symm

/-- On sections over an open `W ⊆ V`, the comparison `modulePushforwardRestrictIso` is the
restriction map of the sheaf of modules along the identification `f⁻¹(W) = (f|_U)⁻¹(W)` of
opens of `X` supplied by `restrictOpensIso` — that is, the identity on sections.  This
characterizes the comparison and rules out multiplication by an automorphism. -/
theorem modulePushforwardRestrictIso_hom_app_val_app
    (M : SheafOfModules.{u} (structureSheafRing X))
    (W : (Opens ((restrictToOpen Y V : TopCat) : Type u))ᵒᵖ)
    (x : ((moduleRestriction X (preimageOpen f V) ⋙
      modulePushforward (restrictedMorphism f V)).obj M).val.obj W) :
    ((modulePushforwardRestrictIso f V).hom.app M).val.app W x =
      M.val.map ((restrictOpensIso f V).hom.app W.unop).op x :=
  rfl

/-- The restriction maps of a sheaf of modules along an equality of opens are the identity,
up to the transport of the type of sections. -/
theorem heq_val_map_eqToHom {T : Type u} [TopologicalSpace T]
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} R)
    {A B : Opens T} (h : A = B) (x : M.val.obj (op B)) :
    HEq (M.val.map (eqToHom h).op x) x := by
  subst h
  rw [eqToHom_refl, op_id]
  simp only [PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply]
  exact HEq.rfl

/-- The comparison `modulePushforwardRestrictIso` is the identity on sections, in the form of
a heterogeneous equality: the two types of sections over an open `W ⊆ V` are the sections of
the sheaf of modules over the same open of `X`, written in two ways. -/
theorem modulePushforwardRestrictIso_hom_app_val_app_heq
    (M : SheafOfModules.{u} (structureSheafRing X))
    (W : (Opens ((restrictToOpen Y V : TopCat) : Type u))ᵒᵖ)
    (x : ((moduleRestriction X (preimageOpen f V) ⋙
      modulePushforward (restrictedMorphism f V)).obj M).val.obj W) :
    HEq (((modulePushforwardRestrictIso f V).hom.app M).val.app W x) x := by
  rw [modulePushforwardRestrictIso_hom_app_val_app]
  exact heq_val_map_eqToHom M
    (isOpenEmbeddingFunctor_obj_map_restrictedMorphismBase f V W.unop).symm x

/-- Pushforward along the restricted morphism is a right adjoint. -/
noncomputable instance modulePushforwardRestrictedMorphism_isRightAdjoint :
    (modulePushforward (restrictedMorphism f V)).IsRightAdjoint :=
  modulePushforward_isRightAdjoint _

/-- Pushforward along the restricted morphism is additive. -/
noncomputable instance modulePushforwardRestrictedMorphism_additive :
    (modulePushforward (restrictedMorphism f V)).Additive :=
  modulePushforward_additive _

/-- Restriction to `V` passes through the ordinary right derived functors of `f_*`: the
`p`-th right derived functor of `f_*`, followed by restriction to `V`, is the `p`-th right
derived functor of the composite `ℱ ↦ (f|_{f⁻¹(V)})_*(ℱ|_{f⁻¹(V)})`.  This holds because
restriction to `V` is exact; it is the half of Stacks 01E5 that does not need restriction to
preserve injectives. -/
noncomputable def rightDerivedPushforwardRestrictIso (p : ℕ) :
    (modulePushforward f).rightDerived p ⋙ moduleRestriction Y V ≅
      (moduleRestriction X (preimageOpen f V) ⋙
        modulePushforward (restrictedMorphism f V)).rightDerived p :=
  have := moduleRestriction_preservesHomology Y V
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _
    (modulePushforwardRestrictIso f V).symm p

end Comparison

section DerivedGeneral

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- An exact additive functor preserves quasi-isomorphisms of bounded below complexes, hence
induces a morphism of localizers on the bounded below homotopy categories. -/
theorem quasiIso_mapHomotopyCategoryPlus_map {K L : HomotopyCategory.Plus A} (φ : K ⟶ L)
    (hφ : HomotopyCategory.Plus.quasiIso A φ) :
    HomotopyCategory.Plus.quasiIso B (F.mapHomotopyCategoryPlus.map φ) := by
  rw [HomotopyCategory.Plus.quasiIso_iff] at hφ ⊢
  have h : (F.mapHomotopyCategoryPlus.map φ).hom =
      (F.mapHomotopyCategory (ComplexShape.up ℤ)).map φ.hom := rfl
  rw [h]
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective φ.hom
  rw [← hg]
  have hq : HomologicalComplex.quasiIso A (ComplexShape.up ℤ) g :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff g).mp (by rw [hg]; exact hφ)
  have hq2 : QuasiIso g := by rwa [← HomologicalComplex.mem_quasiIso_iff]
  have hq3 : HomologicalComplex.quasiIso B (ComplexShape.up ℤ)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
    rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g)).mpr hq3

/-- **The bounded below right derived functor of an exact functor is the functor itself.**  If
`F` is additive and exact then `F.rightDerivedFunctorPlusUnith` is an isomorphism, not merely on
complexes of injectives: applying `F` termwise already inverts quasi-isomorphisms, so the
termwise functor satisfies the universal property of the right derived functor. -/
theorem isIso_rightDerivedFunctorPlusUnit [EnoughInjectives A] :
    IsIso F.rightDerivedFunctorPlusUnith := by
  have hinv : (HomotopyCategory.Plus.quasiIso A).IsInvertedBy
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := fun _ _ φ hφ =>
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      (quasiIso_mapHomotopyCategoryPlus_map F φ hφ)
  exact Functor.isIso_of_isRightDerivedFunctor_of_inverts _ _ hinv

end DerivedGeneral

section DerivedRestriction

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (U : Opens X)

/-- Since restriction to an open subspace is exact, its derived-functor unit is an isomorphism
on every bounded below complex, not just on complexes of injectives. -/
theorem moduleRestrictionRightDerivedFunctorPlusUnit_isIso :
    IsIso (moduleRestriction X U).rightDerivedFunctorPlusUnith := by
  have := moduleRestriction_preservesHomology X U
  exact isIso_rightDerivedFunctorPlusUnit _

attribute [local instance] moduleRestriction_preservesHomology
  moduleRestrictionRightDerivedFunctorPlusUnit_isIso

/-- The canonical bridge from termwise restriction on bounded below homotopy categories to the
right derived restriction functor, induced by the derived-functor unit. -/
noncomputable def moduleRestrictionDerivedTermwiseIso :
    (moduleRestriction X U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ (moduleRestriction X U).rightDerivedFunctorPlus :=
  asIso (moduleRestriction X U).rightDerivedFunctorPlusUnith

/-- **On bounded below cochain complexes, derived restriction is ordinary termwise
restriction.**  Both sides use the localization through the bounded below homotopy category;
in particular no derived pullback is needed to describe the restriction of a bounded below
complex of sheaves of modules to an open subspace. -/
noncomputable def moduleRestrictionDerivedCochainIso :
    (moduleRestriction X U).mapCochainComplexPlus ⋙
        HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ≅
      HomotopyCategory.Plus.quotient _ ⋙ DerivedCategory.Plus.Qh ⋙
        (moduleRestriction X U).rightDerivedFunctorPlus := by
  let e : (moduleRestriction X U).mapCochainComplexPlus ⋙
        HomotopyCategory.Plus.quotient _ ≅
      HomotopyCategory.Plus.quotient _ ⋙
        (moduleRestriction X U).mapHomotopyCategoryPlus :=
    ((HomotopyCategory.Plus.fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (CochainComplex.Plus.ι _)
        ((moduleRestriction X U).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm)
  exact (Functor.isoWhiskerRight e DerivedCategory.Plus.Qh).trans
    (Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient _)
      (moduleRestrictionDerivedTermwiseIso X U))

end DerivedRestriction

end Stacks.Cohomology.HigherDirectImage

end
