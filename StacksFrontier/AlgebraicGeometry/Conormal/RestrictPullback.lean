module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of modules along an open immersion is restriction, and its base change

Let `i : Z ⟶ X` be a morphism of ringed spaces, let `U` be an open subspace of `X` and write
`V = i⁻¹U`. `StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPushforward` proves the
base-change square for *pushforward*, `(i_*F)|_U ≅ (i|_V)_*(F|_V)`. This file proves the
*pullback* analogue, `(i^*M)|_V ≅ (i|_V)^*(M|_U)`.

The pullback statement is not the mate of the pushforward one: restriction to an open subspace
appears in both as a *left* adjoint, so the two squares are not related by the mate
correspondence. What does the work here is a fact about restriction that the pushforward square
did not need:

* restriction of modules to `U` is **left adjoint** to pushforward along the open immersion
  `ι_U : X|_U ⟶ X`. Both functors are `CategoryTheory.SheafOfModules.pushforward`, along the
  two adjoint functors on opens `ι_U(-) ⊣ ι_U⁻¹(-)` of
  `TopologicalSpace.IsOpenMap.adjunction`, so this is an instance of Mathlib's
  `CategoryTheory.SheafOfModules.pushforwardPushforwardAdj`. The orientation matters and is
  easy to get backwards: it is *restriction* that is the left adjoint.

Uniqueness of left adjoints then identifies `ι_U^*` with restriction, and the pullback square
follows from the composition law for pullback together with the commuting square of ringed
spaces `i|_V ≫ ι_U = ι_V ≫ i`, which is proved here.

## Main definitions

* `AlgebraicGeometry.RingedSpace.moduleRestrict` is restriction of sheaves of modules to an open
  subspace, stated at the `structureSheafRing` types. It is
  `AlgebraicGeometry.RingedSpace.restrictModules` by definition.
* `AlgebraicGeometry.RingedSpace.restrictOpensAdjunction` is the adjunction
  `ι_U(-) ⊣ ι_U⁻¹(-)` on opens, with its right-hand functor written as the one that pushforward
  along `ι_U` uses.
* `AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction` is the adjunction
  `(-)|_U ⊣ (ι_U)_*`.
* `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` is the identification
  `ι_U^* ≅ (-)|_U` of pullback along an open immersion with restriction.
* `AlgebraicGeometry.RingedSpace.restrictPullbackIso` is the base-change square
  `i^* ⋙ (-)|_V ≅ (-)|_U ⋙ (i|_V)^*`.
* `AlgebraicGeometry.RingedSpace.modulePullbackPushforwardCounitOfRestrictIso` is the counit
  `ι_U^*((ι_U)_* N) ≅ N`, and
  `AlgebraicGeometry.RingedSpace.modulePullbackUnitOfRestrictIso` is `ι_U^* 𝒪_X ≅ 𝒪_{X|U}`.
  Both are isomorphisms because `ι_U` is an open immersion.

## Main results

* `AlgebraicGeometry.RingedSpace.moduleRestrict_obj_val_obj` and
  `AlgebraicGeometry.RingedSpace.moduleRestrict_obj_unit`: the sections of `M|_U` over an open
  `W` of `U` are the sections of `M` over `ι_U W`, and `𝒪_X|_U` is `𝒪_{X|U}`. Both hold by
  `rfl`.
* `AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_unit_val_app` and
  `AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_counit_val_app` compute the unit and
  counit of `(-)|_U ⊣ (ι_U)_*` on sections: both are restriction of sections of the original
  module along an inclusion of opens. These, with
  `AlgebraicGeometry.RingedSpace.unit_modulePullbackRestrictIso_hom_app`, pin down
  `modulePullbackRestrictIso`: a bundled isomorphism of functors whose type does not mention its
  characterisation asserts nothing by itself.
* `AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict` is the commuting square
  `i|_V ≫ ι_U = ι_V ≫ i` of ringed spaces.
* `AlgebraicGeometry.RingedSpace.moduleRestrict_preservesFiniteLimits`: restriction to an open
  subspace is left exact. Sections-wise it changes nothing, so this is
  `CategoryTheory.PresheafOfModules.evaluationJointlyReflectsLimits`.
* **Pullback along an open immersion is a localization**:
  `AlgebraicGeometry.RingedSpace.isIso_moduleRestrictAdjunction_counit_app` and
  `AlgebraicGeometry.RingedSpace.isIso_modulePullbackPushforwardAdjunction_counit_app_ofRestrict`
  say the counits of `(-)|_U ⊣ (ι_U)_*` and of `ι_U^* ⊣ (ι_U)_*` are isomorphisms, i.e. that
  `(ι_U)_*` is fully faithful;
  `AlgebraicGeometry.RingedSpace.isIso_modulePullbackUnitToUnit_ofRestrict` says the transpose
  `ι_U^* 𝒪_X ⟶ 𝒪_{X|U}` of the structure-sheaf map is an isomorphism; and
  `AlgebraicGeometry.RingedSpace.modulePullback_ofRestrict_preservesFiniteLimits` says `ι_U^*`
  is left exact. Those three facts are what
  `StacksFrontier.AlgebraicGeometry.Conormal.OpenFactorization` needs in order to compare the
  ideal sheaves, and hence the conormal sheaves, of the two sides of a factorization
  `i = i' ≫ ι_U`.
* `CategoryTheory.SheafOfModules.isIso_of_isIso_toPresheaf_app` is the criterion used to prove
  the first of those: a morphism of sheaves of modules is an isomorphism as soon as it is one on
  underlying presheaves of abelian groups.

## Implementation notes

`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict` is the square that
`StacksFrontier.Topology.Sheaves.RingedSpace.RestrictMorphism` deliberately does not record,
because `AlgebraicGeometry.SheafedSpace.ext` reduces it to a comparison of structure-sheaf maps
across an `CategoryTheory.eqToHom`. The comparison is nevertheless elementary once isolated:
both sides are the structure-sheaf map of `i` followed by a restriction of sections, and
restrictions between fixed opens are unique because the hom types of `TopologicalSpace.Opens`
are subsingletons. That is
`AlgebraicGeometry.RingedSpace.hom_c_app_comp_map_eq`, stated away from any restriction
machinery; applying it to the square is a single `exact`, since `rw` cannot build a motive here
(the carrier of a restricted space has two definitionally equal spellings, so the goal is not
type-correct at `implicit` transparency).

For the same reason `AlgebraicGeometry.RingedSpace.isContinuous_restrictOpensInclusion` is
imported as a *local* instance rather than restated: continuity of the inclusion functor on
opens is not an instance in this development, and a copy stated at the other spelling of the
site would not discharge the goals here.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

universe u

/-- **A morphism of sheaves of modules which is an isomorphism on underlying presheaves of
abelian groups is an isomorphism.** The forgetful functor to presheaves of abelian groups
reflects isomorphisms, and a morphism of presheaves is an isomorphism exactly when each of its
components is.

This is the criterion Mathlib does not state in this form, and the only way available here to
recognise an isomorphism of sheaves of modules from its effect on sections: the restriction maps
of a presheaf of modules carry a `CategoryTheory.ModuleCat.restrictScalars` in their types, so
the corresponding statement about `CategoryTheory.ModuleCat` morphisms cannot even be written
down. -/
theorem _root_.CategoryTheory.SheafOfModules.isIso_of_isIso_toPresheaf_app {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    (h : ∀ W, IsIso (((PresheafOfModules.toPresheaf _).map φ.val).app W)) : IsIso φ := by
  rwa [← isIso_iff_of_reflects_iso _ (SheafOfModules.forget.{u} R ⋙
    PresheafOfModules.toPresheaf _), NatTrans.isIso_iff_isIso_app]

attribute [local instance] isContinuous_restrictOpensInclusion

/-! ### Restriction of modules at the `structureSheafRing` types -/

section Restrict

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- The datum along which restriction of modules to an open subspace is a pushforward: the
identity of `𝒪_{X|U}`, which is the pushforward of `𝒪_X` along the inclusion functor on opens
because `𝒪_{X|U}(W) = 𝒪_X(ι_U W)` by definition. -/
def moduleRestrictData :
    structureSheafRing (X.restrict U.isOpenEmbedding) ⟶
      ((restrictOpensInclusion X U).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafRing X) :=
  𝟙 _

/-- **Restriction of sheaves of modules to an open subspace** of a ringed space, written at the
`structureSheafRing` types rather than at the
`StacksDraft.Ch20.Sec46.Tag08C5` ones.

This is `AlgebraicGeometry.RingedSpace.restrictModules` — see
`AlgebraicGeometry.RingedSpace.moduleRestrict_eq_restrictModules` — restated so that the
pullback and pushforward functors of `RingedSpaceModuleAdjunction` can be composed with it
without crossing between two spellings of the structure sheaf of rings, which typeclass
resolution does not see through. -/
def moduleRestrict :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)) :=
  SheafOfModules.pushforward (moduleRestrictData X U)

/-- `moduleRestrict` is `AlgebraicGeometry.RingedSpace.restrictModules`: the two differ only in
whether the structure sheaf of rings is spelled `structureSheafRing` or
`StrictlyPerfect.structureSheafOfRings`, and those are the same definition. -/
theorem moduleRestrict_eq_restrictModules : moduleRestrict X U = restrictModules X U := rfl

/-- **The sections of `M|_U`.** Over an open `W` of `U` they are the sections of `M` over the
corresponding open `ι_U W` of `X`. -/
theorem moduleRestrict_obj_val_obj (M : SheafOfModules.{u} (structureSheafRing X))
    (W : (Opens (X.restrict U.isOpenEmbedding).carrier)ᵒᵖ) :
    ((moduleRestrict X U).obj M).val.obj W =
      M.val.obj (op ((restrictOpensInclusion X U).obj W.unop)) :=
  rfl

/-- **Restriction takes `𝒪_X` to `𝒪_{X|U}`**, on the nose: the structure sheaf of the open
subspace is by definition the restriction of the structure sheaf. -/
theorem moduleRestrict_obj_unit :
    (moduleRestrict X U).obj (SheafOfModules.unit (structureSheafRing X)) =
      SheafOfModules.unit (structureSheafRing (X.restrict U.isOpenEmbedding)) :=
  rfl

/-! ### Restriction is left adjoint to pushforward along the open immersion -/

/-- **The adjunction on opens** underlying the whole file: taking the image of an open of `U`
and taking the preimage of an open of `X` are adjoint, `ι_U(-) ⊣ ι_U⁻¹(-)`.

This is `TopologicalSpace.IsOpenMap.adjunction`, with its two functors written as the ones that
restriction of modules and pushforward along `ι_U : X|_U ⟶ X` respectively use. -/
def restrictOpensAdjunction :
    restrictOpensInclusion X U ⊣ opensMap (X.ofRestrict U.isOpenEmbedding) :=
  U.isOpenEmbedding.isOpenMap.adjunction

/-- The first compatibility condition of
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` for
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction`: the structure-sheaf map of
`ι_U : X|_U ⟶ X` is restriction of sections along the counit `ι_U(ι_U⁻¹A) ≤ A`. This is how
`AlgebraicGeometry.PresheafedSpace.ofRestrict` is defined, so it holds by `rfl`. -/
theorem counit_whiskerRight_eq_structureSheafHom_ofRestrict :
    Functor.whiskerRight (NatTrans.op (restrictOpensAdjunction X U).counit)
        (structureSheafRing X).obj =
      (structureSheafHom (X.ofRestrict U.isOpenEmbedding)).hom ≫
        (opensMap (X.ofRestrict U.isOpenEmbedding)).op.whiskerLeft
          (moduleRestrictData X U).hom := by
  ext1
  funext _
  rfl

/-- A presheaf on the opens of a space sends a composite of restrictions to the restriction
between the same opens. -/
private theorem map_comp_eq_map {C : Type*} [Category C] {T : Type*} [TopologicalSpace T]
    (F : (Opens T)ᵒᵖ ⥤ C) {A B D : (Opens T)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) :
    F.map f ≫ F.map g = F.map h := by
  rw [← F.map_comp]
  exact congrArg F.map (Subsingleton.elim _ _)

/-- The second compatibility condition of
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` for
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction`: restricting sections of `𝒪_X` from
`ι_U W` to `ι_U(ι_U⁻¹(ι_U W))` and back is the identity, because the two opens are equal and
restrictions between fixed opens are unique. -/
theorem moduleRestrictData_whiskerLeft_structureSheafHom_comp :
    (moduleRestrictData X U).hom ≫
      (restrictOpensInclusion X U).op.whiskerLeft
          (structureSheafHom (X.ofRestrict U.isOpenEmbedding)).hom ≫
        Functor.whiskerRight (NatTrans.op (restrictOpensAdjunction X U).unit)
          (structureSheafRing (X.restrict U.isOpenEmbedding)).obj = 𝟙 _ := by
  ext1
  funext _
  exact (map_comp_eq_map (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) _ _ _).trans
    (CategoryTheory.Functor.map_id _ _)

/-- **Restriction of modules to an open subspace is left adjoint to pushforward along the open
immersion**, `(-)|_U ⊣ (ι_U)_*`.

Both functors are `CategoryTheory.SheafOfModules.pushforward`, along the two adjoint functors on
opens of `AlgebraicGeometry.RingedSpace.restrictOpensAdjunction`, so this is Mathlib's
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj`. Note the orientation: restriction is
the *left* adjoint here, which is why pullback along an open immersion is restriction
(`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso`) rather than pushforward along one
being restriction. -/
@[sga "4 IV 13.4" "special case", sga "4 Vbis 1.3.6" "special case"]
def moduleRestrictAdjunction :
    moduleRestrict X U ⊣ modulePushforward (X.ofRestrict U.isOpenEmbedding) :=
  SheafOfModules.pushforwardPushforwardAdj (restrictOpensAdjunction X U) (moduleRestrictData X U)
    (structureSheafHom (X.ofRestrict U.isOpenEmbedding))
    (counit_whiskerRight_eq_structureSheafHom_ofRestrict X U)
    (moduleRestrictData_whiskerLeft_structureSheafHom_comp X U)

/-- **The unit of `(-)|_U ⊣ (ι_U)_*` on sections.** For a section of `M` over an open `A` of
`X` it is restriction to `ι_U(ι_U⁻¹A)`, the largest open of `A` lying in `U`. -/
theorem moduleRestrictAdjunction_unit_val_app (M : SheafOfModules.{u} (structureSheafRing X))
    (A : (Opens X.carrier)ᵒᵖ) (x : M.val.obj A) :
    ((moduleRestrictAdjunction X U).unit.app M).val.app A x =
      M.val.map ((restrictOpensAdjunction X U).counit.app A.unop).op x :=
  rfl

/-- **The counit of `(-)|_U ⊣ (ι_U)_*` on sections.** It is restriction along the unit
`W ≤ ι_U⁻¹(ι_U W)` of the adjunction on opens, which is an equality; so the counit is an
isomorphism, as it must be for an open immersion. -/
theorem moduleRestrictAdjunction_counit_val_app
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)))
    (W : (Opens (X.restrict U.isOpenEmbedding).carrier)ᵒᵖ)
    (x : ((moduleRestrict X U).obj
      ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj N)).val.obj W) :
    ((moduleRestrictAdjunction X U).counit.app N).val.app W x =
      N.val.map ((restrictOpensAdjunction X U).unit.app W.unop).op x :=
  rfl

/-- **Pullback along an open immersion is restriction**, `ι_U^* ≅ (-)|_U`.

Both functors are left adjoint to pushforward along `ι_U : X|_U ⟶ X`, by
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` and
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction`, so uniqueness of left adjoints
supplies a canonical isomorphism. It is pinned by
`AlgebraicGeometry.RingedSpace.unit_modulePullbackRestrictIso_hom_app`, which together with
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_unit_val_app` determines it. -/
def modulePullbackRestrictIso :
    modulePullback (X.ofRestrict U.isOpenEmbedding) ≅ moduleRestrict X U :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction _) (moduleRestrictAdjunction X U)

/-- **The characterisation of `modulePullbackRestrictIso`.** Composed with the unit of
`ι_U^* ⊣ (ι_U)_*` it is the unit of `(-)|_U ⊣ (ι_U)_*`, whose effect on sections is
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_unit_val_app`.

Since a unit determines its left adjoint up to unique isomorphism, this fixes
`modulePullbackRestrictIso` completely. -/
theorem unit_modulePullbackRestrictIso_hom_app (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).unit.app M ≫
        (modulePushforward (X.ofRestrict U.isOpenEmbedding)).map
          ((modulePullbackRestrictIso X U).hom.app M) =
      (moduleRestrictAdjunction X U).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- `modulePullbackRestrictIso` is compatible with the counits of the two adjunctions as well.
This is the dual half of `unit_modulePullbackRestrictIso_hom_app`. -/
theorem modulePullbackRestrictIso_hom_app_counit
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    (modulePullbackRestrictIso X U).hom.app
          ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj N) ≫
        (moduleRestrictAdjunction X U).counit.app N =
      (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).counit.app N :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ N

/-- Restriction to an open subspace preserves zero morphisms: it does not change the underlying
maps on sections, only the opens they are indexed by. -/
instance moduleRestrict_preservesZeroMorphisms :
    (moduleRestrict X U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **Restriction to an open subspace is left exact.** It does not change sections, only the
opens they are indexed by, so a limit cone of sheaves of modules — which is computed
sectionwise — stays a limit cone. -/
instance moduleRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (moduleRestrict X U) := by
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  exact ⟨isLimitOfReflects (SheafOfModules.forget _)
    (PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun W =>
      isLimitOfPreserves (SheafOfModules.evaluation (structureSheafRing X)
        (op ((restrictOpensInclusion X U).obj W.unop))) hc)⟩

/-! ### Pullback along an open immersion is a localization -/

/-- **The unit of `ι_U(-) ⊣ ι_U⁻¹(-)` is an isomorphism**: for an open `W` of `U` the open
`ι_U⁻¹(ι_U W)` of `U` is `W` again, because `ι_U` is injective.

This is what makes pullback along an open immersion a localization: by
`AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_counit_val_app` the counit of
`(-)|_U ⊣ (ι_U)_*` is restriction of sections along this inclusion of opens. -/
instance isIso_restrictOpensAdjunction_unit_app
    (W : Opens (X.restrict U.isOpenEmbedding).carrier) :
    IsIso ((restrictOpensAdjunction X U).unit.app W) := by
  refine ⟨homOfLE ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rintro x ⟨y, hy, he⟩
  exact (Subtype.ext he.symm : x = y) ▸ hy

/-- `AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_counit_val_app` read on the
underlying presheaves of abelian groups rather than on elements: the counit of
`(-)|_U ⊣ (ι_U)_*` at `N` is the restriction map of `N` along `W ≤ ι_U⁻¹(ι_U W)`.

Stated through `CategoryTheory.PresheafOfModules.toPresheaf` because the restriction map of a
presheaf *of modules* has a `CategoryTheory.ModuleCat.restrictScalars` in its type, so the
corresponding equation of `CategoryTheory.ModuleCat` morphisms is not type-correct as written.
Forgetting the module structures removes that dependency and loses nothing: a morphism of
sheaves of modules is an isomorphism as soon as it is one on underlying abelian groups. -/
theorem moduleRestrictAdjunction_counit_toPresheaf_app
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)))
    (W : (Opens (X.restrict U.isOpenEmbedding).carrier)ᵒᵖ) :
    ((PresheafOfModules.toPresheaf _).map
        ((moduleRestrictAdjunction X U).counit.app N).val).app W =
      ((PresheafOfModules.toPresheaf _).obj N.val).map
        ((restrictOpensAdjunction X U).unit.app W.unop).op :=
  rfl

/-- **The counit of `(-)|_U ⊣ (ι_U)_*` is an isomorphism**, i.e. `(ι_U)_*` is fully faithful:
the sections of `((ι_U)_* N)|_U` over an open `W` of `U` are the sections of `N` over
`ι_U⁻¹(ι_U W) = W`, and the counit is that identification. -/
instance isIso_moduleRestrictAdjunction_counit_app
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    IsIso ((moduleRestrictAdjunction X U).counit.app N) :=
  SheafOfModules.isIso_of_isIso_toPresheaf_app _ fun W => by
    rw [moduleRestrictAdjunction_counit_toPresheaf_app]
    exact ((PresheafOfModules.toPresheaf _).obj N.val).map_isIso
      ((restrictOpensAdjunction X U).unit.app W.unop).op

/-- The components of `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` are
isomorphisms, being the components of an isomorphism of functors. Stated so that instance
search can use it: the isomorphism is bundled as an `CategoryTheory.Iso` of functors, whose
`hom` applied at an object is not of the shape instance search unfolds to. -/
instance isIso_modulePullbackRestrictIso_hom_app (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsIso ((modulePullbackRestrictIso X U).hom.app M) :=
  inferInstanceAs (IsIso ((modulePullbackRestrictIso X U).app M).hom)

/-- **The counit of `ι_U^* ⊣ (ι_U)_*` is an isomorphism.** Through
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso_hom_app_counit` it is the counit of
`(-)|_U ⊣ (ι_U)_*` preceded by an isomorphism, and that counit is
`AlgebraicGeometry.RingedSpace.isIso_moduleRestrictAdjunction_counit_app`. -/
instance isIso_modulePullbackPushforwardAdjunction_counit_app_ofRestrict
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    IsIso ((modulePullbackPushforwardAdjunction
      (X.ofRestrict U.isOpenEmbedding)).counit.app N) := by
  rw [← modulePullbackRestrictIso_hom_app_counit X U N]
  infer_instance

/-- **`ι_U^* ((ι_U)_* N) ≅ N`**, the counit of `ι_U^* ⊣ (ι_U)_*` as an isomorphism. -/
def modulePullbackPushforwardCounitOfRestrictIso
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).obj
        ((modulePushforward (X.ofRestrict U.isOpenEmbedding)).obj N) ≅ N :=
  asIso ((modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).counit.app N)

/-- The forward map of `modulePullbackPushforwardCounitOfRestrictIso X U N` is the counit of
`ι_U^* ⊣ (ι_U)_*` at `N`. -/
@[simp]
theorem modulePullbackPushforwardCounitOfRestrictIso_hom
    (N : SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :
    (modulePullbackPushforwardCounitOfRestrictIso X U N).hom =
      (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).counit.app N :=
  rfl

/-- The unit of `(-)|_U ⊣ (ι_U)_*` at the structure sheaf is the structure-sheaf map of
`ι_U : X|_U ⟶ X`. Both restrict a section of `𝒪_X` over an open `A` to the open
`ι_U(ι_U⁻¹A)`, so this holds by `rfl`. -/
theorem moduleRestrictAdjunction_unit_app_unit :
    (moduleRestrictAdjunction X U).unit.app (SheafOfModules.unit (structureSheafRing X)) =
      structureSheafModuleHom (X.ofRestrict U.isOpenEmbedding) :=
  rfl

/-- **`ι_U^* 𝒪_X ⟶ 𝒪_{X|U}` is the identification `ι_U^* ≅ (-)|_U` at the structure sheaf.**
Both are transposes under `ι_U^* ⊣ (ι_U)_*` of the structure-sheaf map of `ι_U`: for the
left-hand side by `RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit`, for
the right-hand side by `AlgebraicGeometry.RingedSpace.unit_modulePullbackRestrictIso_hom_app`
together with `AlgebraicGeometry.RingedSpace.moduleRestrictAdjunction_unit_app_unit`. -/
theorem modulePullbackUnitToUnit_ofRestrict :
    modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding) =
      (modulePullbackRestrictIso X U).hom.app (SheafOfModules.unit (structureSheafRing X)) :=
  ((modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)).homEquiv
      _ _).injective
    ((homEquiv_modulePullbackUnitToUnit _).trans
      (((moduleRestrictAdjunction_unit_app_unit X U).symm.trans
        (unit_modulePullbackRestrictIso_hom_app X U _).symm).trans
          (Adjunction.homEquiv_unit _ _ _ _).symm))

/-- **The transpose `ι_U^* 𝒪_X ⟶ 𝒪_{X|U}` of the structure-sheaf map of an open immersion is
an isomorphism**, by `AlgebraicGeometry.RingedSpace.modulePullbackUnitToUnit_ofRestrict`. -/
instance isIso_modulePullbackUnitToUnit_ofRestrict :
    IsIso (modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding)) := by
  rw [modulePullbackUnitToUnit_ofRestrict]
  exact isIso_modulePullbackRestrictIso_hom_app X U _

/-- **`ι_U^* 𝒪_X ≅ 𝒪_{X|U}`**, the transpose of the structure-sheaf map of `ι_U` as an
isomorphism. -/
def modulePullbackUnitOfRestrictIso :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).obj
        (SheafOfModules.unit (structureSheafRing X)) ≅
      SheafOfModules.unit (structureSheafRing (X.restrict U.isOpenEmbedding)) :=
  asIso (modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding))

/-- The forward map of `modulePullbackUnitOfRestrictIso X U` is
`modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding)`. -/
@[simp]
theorem modulePullbackUnitOfRestrictIso_hom :
    (modulePullbackUnitOfRestrictIso X U).hom =
      modulePullbackUnitToUnit (X.ofRestrict U.isOpenEmbedding) :=
  rfl

/-- Pullback along an open immersion preserves zero morphisms, being isomorphic to restriction
(`AlgebraicGeometry.RingedSpace.moduleRestrict_preservesZeroMorphisms`). -/
instance modulePullback_ofRestrict_preservesZeroMorphisms :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (modulePullbackRestrictIso X U).symm

/-- **Pullback along an open immersion is left exact**, being isomorphic to restriction
(`AlgebraicGeometry.RingedSpace.moduleRestrict_preservesFiniteLimits`). -/
instance modulePullback_ofRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (modulePullback (X.ofRestrict U.isOpenEmbedding)) :=
  preservesFiniteLimits_of_natIso (modulePullbackRestrictIso X U).symm

end Restrict

/-! ### The commuting square of ringed spaces -/

section Square

variable {Z X : RingedSpace.{u, u}}

/-- **Two restrictions of sections along a morphism of ringed spaces agree.** Given
`i : Z ⟶ X`, a section of `𝒪_X` over an open `A` may be carried to a section of `𝒪_Z` over an
open `B ⊆ i⁻¹A` either by applying `i^♯` over `A` and restricting, or by first restricting to a
smaller open `A'` of `X`, applying `i^♯` there, and restricting; the two agree.

This is the naturality of `i^♯` together with the uniqueness of restriction maps between fixed
opens, and it is the only content of
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict`. It is stated away from any
restriction machinery because at the restricted spaces the corresponding goal is not
type-correct at `implicit` transparency, so it cannot be proved by `rw` in place. -/
theorem hom_c_app_comp_map_eq (i : Z ⟶ X) {A A' : (Opens X.carrier)ᵒᵖ} (f : A ⟶ A')
    {B B' : (Opens Z.carrier)ᵒᵖ} (p : (Opens.map i.hom.base).op.obj A ⟶ B) (p' : B ⟶ B')
    (q : (Opens.map i.hom.base).op.obj A' ⟶ B') :
    i.hom.c.app A ≫ Z.presheaf.map p ≫ Z.presheaf.map p' =
      X.presheaf.map f ≫ i.hom.c.app A' ≫ Z.presheaf.map q := by
  rw [← Category.assoc (X.presheaf.map f), i.hom.c.naturality f, Category.assoc,
    map_comp_eq_map _ p p' (p ≫ p')]
  exact congrArg _ (map_comp_eq_map _ _ q _).symm

/-- **The restriction square of ringed spaces**, `i|_V ≫ ι_U = ι_V ≫ i` for `V = i⁻¹U`.

`StacksFrontier.Topology.Sheaves.RingedSpace.RestrictMorphism` constructs `i|_V` but does not state
this square, because `AlgebraicGeometry.SheafedSpace.ext` turns it into a comparison of
structure-sheaf maps across an `CategoryTheory.eqToHom`. That comparison is
`AlgebraicGeometry.RingedSpace.hom_c_app_comp_map_eq`; the underlying continuous maps agree by
`rfl`. The square is what makes the pullback base-change square
`AlgebraicGeometry.RingedSpace.restrictPullbackIso` available. -/
theorem restrictHom_comp_ofRestrict (i : Z ⟶ X) (U : Opens X.carrier) :
    restrictHom i U ≫ X.ofRestrict U.isOpenEmbedding =
      Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding ≫ i := by
  symm
  refine SheafedSpace.ext _ _ rfl (NatTrans.ext (funext fun A => ?_))
  exact hom_c_app_comp_map_eq i (U.isOpenEmbedding.isOpenMap.adjunction.counit.app A.unop).op
    _ _ _

/-! ### The pullback base-change square -/

/-- **`(i^*M)|_V ≅ (i|_V)^*(M|_U)`**, naturally in the `𝒪_X`-module `M`: pulling back along a
morphism of ringed spaces `i : Z ⟶ X` and restricting to `V = i⁻¹U` agrees with restricting to
the open subspace `U` of `X` and pulling back along the restricted morphism
`i|_V : Z|_V ⟶ X|_U`.

This is the pullback analogue of
`AlgebraicGeometry.RingedSpace.restrictPushforwardIso`. It is assembled from
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso`, which turns each restriction into a
pullback along an open immersion, the composition law
`RingedSpaceModuleAdjunction.modulePullbackComp`, and the commuting square
`AlgebraicGeometry.RingedSpace.restrictHom_comp_ofRestrict`. -/
def restrictPullbackIso (i : Z ⟶ X) (U : Opens X.carrier) :
    modulePullback i ⋙ moduleRestrict Z ((Opens.map i.hom.base).obj U) ≅
      moduleRestrict X U ⋙ modulePullback (restrictHom i U) :=
  Functor.isoWhiskerLeft (modulePullback i)
      (modulePullbackRestrictIso Z ((Opens.map i.hom.base).obj U)).symm ≪≫
    (modulePullbackComp (Z.ofRestrict ((Opens.map i.hom.base).obj U).isOpenEmbedding) i).symm ≪≫
    modulePullbackCongr (restrictHom_comp_ofRestrict i U).symm ≪≫
    modulePullbackComp (restrictHom i U) (X.ofRestrict U.isOpenEmbedding) ≪≫
    Functor.isoWhiskerRight (modulePullbackRestrictIso X U) (modulePullback (restrictHom i U))

end Square

end AlgebraicGeometry.RingedSpace

end
